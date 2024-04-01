module REPL where

import Prelude

import Ansi.Codes (Color(..))
import Ansi.Output (foreground, withGraphics)
import Data.Array (filter)
import Data.Array.NonEmpty (NonEmptyArray, foldl1, fromArray, (!!))
import Data.DateTime.Instant (unInstant)
import Data.Either (Either(..))
import Data.List (List(..), intercalate, (:))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), drop, lastIndexOf, length, splitAt, stripPrefix, trim)
import Data.String.Regex (Regex, match, replace)
import Data.String.Regex.Flags (global, noFlags)
import Data.String.Regex.Unsafe (unsafeRegex)
import Data.String.Utils (startsWith, stripMargin)
import Data.Time (diff)
import Data.Time.Duration (Milliseconds(..))
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Class.Console (error)
import Effect.Console (log)
import Effect.Exception (catchException, message, throw, try)
import Effect.Now (now, nowTime)
import Effect.Ref (Ref, modify_, new, read, write)
import Language.CP (compile, deserialize, importDefs, inferType, interpret, serialize, showParseError)
import Language.CP.Context (Mode(..), REPLState, clearEnv, fromState, initState, mergeStates, runChecking, runTyping)
import Language.CP.Util (unsafeFromJust)
import Node.Encoding (Encoding(..))
import Node.EventEmitter (on_)
import Node.FS.Stats (isDirectory, modifiedTime)
import Node.FS.Sync as Sync
import Node.Path (FilePath, concat, dirname, sep)
import Node.Process (cwd, exit)
import Node.ReadLine (Completer, Interface, createConsoleInterface, lineH, noCompletion, prompt, setPrompt)

foreign import require :: forall a. String -> (a -> Effect Unit) -> Effect Unit

-- commands
type Cmd = String -> Ref REPLState -> Effect Unit

printHelp :: Cmd
printHelp _ _ = log $ stripMargin
  """
  |Avaiable commands:
  |  :mode
  |  :mode SmallStep|StepTrace|Elaborate|BigStep|HOAS|Closure
  |  :timing
  |  :env
  |  :env clear
  |  :type <expr>
  |  :import <file>
  |  :load <file>
  |  :compile <file>
  """

showOrSetMode :: Cmd
showOrSetMode arg ref = case arg of
  "" -> do
    st <- read ref
    log $ show st.mode
  "SmallStep" -> set SmallStep
  "StepTrace" -> set StepTrace
  "Elaborate" -> set Elaborate
  "BigStep"   -> set BigStep
  "HOAS"      -> set HOAS
  "Closure"   -> set Closure
  other       -> fatal $ "Invalid mode: " <> other
  where
    set :: Mode -> Effect Unit
    set mode = modify_ (\st -> st { mode = mode }) ref

setTiming :: Cmd
setTiming _ = modify_ (\st -> st { timing = true })

showOrClearEnv :: Cmd
showOrClearEnv arg ref = case arg of
  "" -> do
    st <- read ref
    log $ serialize st
  "clear" -> modify_ clearEnv ref
  other -> fatal $ "Invalid argument: " <> other

typeExpr :: Cmd
typeExpr expr ref = do
  st <- read ref
  case runTyping (inferType expr) (fromState st) of
    Left err -> fatal $ show err
    Right output -> log output

importFile :: Cmd
importFile file ref = do
  code <- readPreCode file
  st <- read ref
  case runChecking (importDefs code) st of
    Left err -> fatal $ show err
    Right (_ /\ st') -> write st' ref

loadFile :: Cmd
loadFile file ref = do
  code <- readPreCode file
  evalProg code ref

evalProg :: Cmd
evalProg code ref = do
  st <- read ref
  case runChecking (interpret code) st of
    Left err -> fatal $ show err
    Right (output /\ st') -> do
      log output
      write st' ref

compileFile :: Cmd
compileFile file ref = do
  beginTime <- nowTime
  compileJS file
  compileTime <- nowTime
  st <- read ref
  let compileSeconds = showSeconds $ diff compileTime beginTime
  if st.runJS then do
    if st.timing then
      info $ "Compile time: " <> compileSeconds
    else pure unit
    workDir <- cwd
    let file' = concat [workDir, extJS file]
    require file' \res -> do
      log res
      endTime <- nowTime
      let runSeconds = showSeconds $ diff endTime compileTime
      if st.timing then
        info $ "Run time: " <> runSeconds
      else pure unit
  else info $ file <> " compiled in " <> compileSeconds
  where
    compileJS :: FilePath -> Effect Unit
    compileJS f = do
      code <- Sync.readTextFile UTF8 f
      st <- loadHeaders code
      program <- importLibs code
      case compile program f st of
        Left err -> throw err
        Right (js /\ h) -> do
          Sync.writeTextFile UTF8 (extJS f) js
          Sync.writeTextFile UTF8 (extHeader f) h
    loadHeaders :: String -> Effect REPLState
    loadHeaders code = matchOpen dir code (const (pure initState)) \n f -> do
      st <- loadHeader f
      st' <- loadHeaders (replace openRegex "" code)
      case mergeStates st st' of
        Right st'' -> pure st''
        Left names -> throw $ intercalate ", " names <> " in "
                           <> show n <> " have been defined"
    loadHeader :: FilePath -> Effect REPLState
    loadHeader f = do
      cp <- Sync.stat f
      header <- try $ Sync.stat (extHeader f)
      case header of
        Right h | modifiedTime cp <= modifiedTime h -> do
          text <- Sync.readTextFile UTF8 (extHeader f)
          text' <- includeHeaders text
          case deserialize text' of
            Left err -> throw $ showParseError err text'
            Right st -> pure st
        _ -> compileJS f *> loadHeader f
    includeHeaders :: String -> Effect String
    includeHeaders code = case match includeRegex code of
      Just arr -> do
        let f = unsafeFromJust $ unsafeFromJust $ arr !! 1
        text <- Sync.readTextFile UTF8 f
        includeHeaders $ replace includeRegex text code
      Nothing -> pure code
    includeRegex :: Regex
    includeRegex = unsafeRegex """include\s+"([^"]+)"\s*;""" noFlags
    importLibs :: String -> Effect String
    importLibs code = matchOpen dir code pure \n f -> do
      instant <- now
      let Milliseconds t = unInstant instant
      workDir <- cwd
      let f' = concat [workDir, f]
      importLibs $ replace openRegex (preludeAll n f' t) code
    preludeAll :: String -> FilePath -> Number -> String
    preludeAll n f t = "{-# PRELUDE H    "
                    <> "include " <> show (extHeader f) <> ";    "
                    <> "#-}    "
                    <> "{-# PRELUDE CP  "
                    <> "import * as " <> n <> " from " <> show (extJS f <> "?t=" <> show t) <> ";  "
                    <> "for (var [key, value] of Object.entries(" <> n <> ")) "
                    <> "{ global[key] = value; }    "
                    <> "#-}"
    dir = dirname file
    extHeader = (_ <> ".h")
    extJS = (_ <> ".mjs")

errorCmd :: Cmd
errorCmd input ref = do
  fatal $ "Invalid command: " <> input
  printHelp "" ref

mayTime :: Cmd -> Cmd
mayTime cmd arg ref = do
  beginTime <- nowTime
  cmd arg ref
  endTime <- nowTime
  st <- read ref
  if st.timing then let seconds = showSeconds $ diff endTime beginTime in
    info $ "Time: " <> seconds
  else pure unit

-- command dispatcher
dispatch :: Cmd
dispatch input = ifMatchesAny (":?" : ":h" : ":help" : Nil) printHelp $
  ifMatchesAny (":q" : ":quit" : ":exit" : Nil) (\_ _ -> exit) $
  ifMatches ":mode" showOrSetMode $
  ifMatches ":timing" setTiming $
  ifMatches ":env" showOrClearEnv $
  ifMatches ":type" (mayTime typeExpr) $
  ifMatches ":import" (mayTime importFile) $
  ifMatches ":load" (mayTime loadFile) $
  ifMatches ":compile" compileFile $
  ifMatches ":" errorCmd $
  mayTime evalProg input
  where
    ifMatchesAny :: forall a. List String -> (String -> a) -> a -> a
    ifMatchesAny Nil _ d = d
    ifMatchesAny (p : ps) f d = case stripPrefix (Pattern p) input of
      Just rest -> f (trim rest)
      Nothing -> ifMatchesAny ps f d
    ifMatches :: forall a. String -> (String -> a) -> a -> a
    ifMatches p f d = ifMatchesAny (p : Nil) f d

handler :: Interface -> Ref REPLState -> String -> Effect Unit
handler interface ref input = do
  catchException (fatal <<< message) (dispatch (trim input) ref)
  prompt interface

-- completers
data Syntax = ConstSyntax String | FileSyntax String

getCompleter :: Syntax -> Completer
getCompleter (ConstSyntax target) input =
  if startsWith input target
  then pure { completions : [target], matched : input }
  else noCompletion ""
getCompleter (FileSyntax s) input = let target = s <> " " in
  if startsWith input target
  then pure { completions : [target], matched : input }
  else if startsWith target input
  then completePath target $ drop (length target) input
  else noCompletion ""
  where
    completePath :: String -> Completer
    completePath cmd path = do
      let dir /\ base = splitPath path
      exists <- Sync.exists dir
      if exists then do
        stat <- Sync.stat dir
        if isDirectory stat then do
          files <- Sync.readdir dir
          let candidates = filter (startsWith base) files
          pure { completions : map (\f -> cmd <> concat [dir, f]) candidates, matched : cmd <> path }
        else noCompletion ""
      else noCompletion ""

    splitPath :: FilePath -> FilePath /\ FilePath
    splitPath path = case lastIndexOf (Pattern sep) path of
        Just i -> let r = splitAt (i + 1) path in r.before /\ r.after
        Nothing -> "." /\ path

mergeCompleter :: Completer -> Completer -> Completer
mergeCompleter c1 c2 input = do
  r1 <- c1 input
  r2 <- c2 input
  pure { completions : r1.completions <> r2.completions, matched : input }

makeCompleter :: NonEmptyArray Syntax -> Completer
makeCompleter rules = foldl1 mergeCompleter $ map getCompleter rules

completer :: Completer
completer = makeCompleter $ unsafeFromJust $ fromArray
  [ ConstSyntax ":help"
  , ConstSyntax ":quit", ConstSyntax ":exit"
  , ConstSyntax ":mode"
  , ConstSyntax ":mode SmallStep"
  , ConstSyntax ":mode StepTrace"
  , ConstSyntax ":mode Elaborate"
  , ConstSyntax ":mode BigStep"
  , ConstSyntax ":mode HOAS"
  , ConstSyntax ":mode Closure"
  , ConstSyntax ":timing"
  , ConstSyntax ":env"
  , ConstSyntax ":env clear"
  , ConstSyntax ":type"
  , FileSyntax ":import"
  , FileSyntax ":load"
  , FileSyntax ":compile"
  ]

repl :: Effect Unit
repl = do
  log "Next-Gen CP REPL, dev version"
  interface <- createConsoleInterface completer
  setPrompt "> " interface
  prompt interface
  ref <- new initState { forbidDup = false, runJS = true }
  on_ lineH (handler interface ref) interface

-- helpers

fatal :: String -> Effect Unit
fatal msg = error $ withGraphics (foreground Red) msg

info :: String -> Effect Unit
info msg = log $ withGraphics (foreground Blue) msg

verb :: String -> Effect Unit
verb msg = log $ withGraphics (foreground BrightBlack) msg

showSeconds :: Milliseconds -> String
showSeconds (Milliseconds n) = show (n / 1000.0) <> "s"

preprocess :: FilePath -> String -> Effect String
preprocess path program = matchOpen path program pure \_ f -> do
  text <- Sync.readTextFile UTF8 f
  preprocess path $ replace openRegex (replace lineRegex " " text) program
  where lineRegex = unsafeRegex """(--.*)?[\r\n]+""" global

matchOpen :: forall a. FilePath -> String -> (String -> Effect a) -> (String -> String -> Effect a) -> Effect a
matchOpen path program miss hit = case match openRegex program of
  Nothing -> miss program
  Just arr -> do
    let name = unsafeFromJust $ unsafeFromJust $ arr !! 1
        file = lib name
    hit name file
  where lib name = concat [path, name <> ".lib"]

openRegex :: Regex
openRegex = unsafeRegex """open\s+(\w+)\s*;""" noFlags

readPreCode :: FilePath -> Effect String
readPreCode f = do
  code <- Sync.readTextFile UTF8 f
  preprocess (dirname f) code

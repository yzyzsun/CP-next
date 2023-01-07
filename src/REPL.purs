module REPL where

import Prelude

import Ansi.Codes (Color(..))
import Ansi.Output (foreground, withGraphics)
import Data.Array (filter)
import Data.Array.NonEmpty (NonEmptyArray, foldl1, fromArray, (!!))
import Data.Either (Either(..))
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), drop, lastIndexOf, length, splitAt, stripPrefix, take, trim)
import Data.String.Regex (match, replace)
import Data.String.Regex.Flags (global, noFlags)
import Data.String.Regex.Unsafe (unsafeRegex)
import Data.String.Utils (startsWith, stripMargin)
import Data.Time (diff)
import Data.Time.Duration (Milliseconds(..))
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Class.Console (error)
import Effect.Console (log)
import Effect.Exception (message, try)
import Effect.Now (nowTime)
import Effect.Ref (Ref, modify_, new, read, write)
import Language.CP (compile, importDefs, inferType, interpret, showTypeError)
import Language.CP.Context (CompilerState, Mode(..), clearEnv, fromState, initState, ppState, runChecking, runTyping)
import Language.CP.Util (unsafeFromJust)
import Node.Encoding (Encoding(..))
import Node.FS.Stats (isDirectory)
import Node.FS.Sync as Sync
import Node.Path (FilePath, concat, sep)
import Node.Process (exit)
import Node.ReadLine (Completer, Interface, createConsoleInterface, noCompletion, prompt, setLineHandler, setPrompt)

foreign import eval :: forall a. String -> a

-- commands
type Cmd = String -> Ref CompilerState -> Effect Unit

printHelp :: Cmd
printHelp _ _ = log $ stripMargin
  """
  |Avaiable commands:
  |  :mode
  |  :mode SmallStep|StepTrace|BigStep|HOAS|Closure
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
    log $ ppState st
  "clear" -> modify_ clearEnv ref
  other -> fatal $ "Invalid argument: " <> other

typeExpr :: Cmd
typeExpr expr ref = do
  st <- read ref
  case runTyping (inferType expr) (fromState st) of
    Left err -> fatal $ showTypeError err
    Right output -> log output

importFile :: Cmd
importFile file ref = do
  code <- readPreCode file
  st <- read ref
  case runChecking (importDefs code) st of
    Left err -> fatal $ showTypeError err
    Right (_ /\ st') -> write st' ref

loadFile :: Cmd
loadFile file ref = do
  code <- readPreCode file
  evalProg code ref

evalProg :: Cmd
evalProg code ref = do
  st <- read ref
  case runChecking (interpret code) st of
    Left err -> fatal $ showTypeError err
    Right (output /\ st') -> do
      log output
      write st' ref

compileFile :: Cmd
compileFile file ref = do
  beginTime <- nowTime
  code <- readPreCode file
  case compile code of
    Left err -> fatal err
    Right js -> do
      verb js
      compileTime <- nowTime
      st <- read ref
      if st.timing then let seconds = showSeconds $ diff compileTime beginTime in
        info $ "Compile time: " <> seconds
      else pure unit
      log $ eval js
      endTime <- nowTime
      if st.timing then let seconds = showSeconds $ diff endTime compileTime in
        info $ "Run time: " <> seconds
      else pure unit

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
  ifMatchesAny (":q" : ":quit" : ":exit" : Nil) (\_ -> \_ -> exit 0) $
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

handler :: Interface -> Ref CompilerState -> String -> Effect Unit
handler interface ref input = do
  dispatch (trim input) ref
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
  , ConstSyntax ":mode SmallStep", ConstSyntax ":mode StepTrace", ConstSyntax ":mode BigStep"
  , ConstSyntax ":mode HOAS", ConstSyntax ":mode Closure"
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
  ref <- new initState
  setLineHandler (handler interface ref) interface

-- helpers

fatal :: String -> Effect Unit
fatal msg = error $ withGraphics (foreground Red) msg

info :: String -> Effect Unit
info msg = log $ withGraphics (foreground Blue) msg

verb :: String -> Effect Unit
verb msg = log $ withGraphics (foreground BrightBlack) msg

showSeconds :: Milliseconds -> String
showSeconds (Milliseconds n) = show (n / 1000.0) <> "s"

readTextFile :: String -> Effect String
readTextFile f = do
  result <- try $ Sync.readTextFile UTF8 f
  case result of Right text -> pure text
                 Left err -> fatal (message err) $> ""

preprocess :: String -> String -> Effect String
preprocess path program = case match openRegex program of
  Just arr -> do
    let name = unsafeFromJust $ unsafeFromJust $ arr !! 1
    text <- readTextFile $ filepath name
    preprocess path $ replace openRegex (replace lineRegex " " text) program
  Nothing -> pure program
  where openRegex = unsafeRegex """open\s+(\w+)\s*;""" noFlags
        lineRegex = unsafeRegex """(--.*)?[\r\n]+""" global
        filepath name = concat [path, name <> ".lib"]

readPreCode :: String -> Effect String
readPreCode f = do
  code <- readTextFile f
  preprocess path code
  where path = case lastIndexOf (Pattern "/") f of
                Just index -> take index f
                Nothing -> ""

module REPL where

import Prelude

import Ansi.Codes (Color(..))
import Ansi.Output (foreground, withGraphics)
import Control.Monad.Except (runExcept)
import Control.Monad.State (runStateT)
import Data.Time (diff)
import Data.Either (Either(..))
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), stripPrefix, trim)
import Data.String.Utils (stripMargin)
import Data.Time.Duration (Milliseconds(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Class.Console (error)
import Effect.Console (log)
import Effect.Exception (message, try)
import Effect.Now (nowTime)
import Effect.Ref (Ref, modify_, new, read, write)
import Language.CP (importDefs, inferType, interpret, showTypeError)
import Language.CP.Context (CompilerState, Mode(..), fromState, initState, ppState, runTyping)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as Sync
import Node.ReadLine (Interface, createConsoleInterface, noCompletion, prompt, setLineHandler, setPrompt)

-- commands
type Cmd = String -> Ref CompilerState -> Effect Unit

printHelp :: Cmd
printHelp _ _ = log $ stripMargin
  """
  |Avaiable commands:
  |  :show mode
  |  :set mode SmallStep|StepTrace|BigStep|HOAS|Closure
  |  :set timing
  |  :show env
  |  :type <expr>
  |  :load <file>
  |  :import <file>
  """

showMode :: Cmd
showMode _ ref = do
  st <- read ref
  log $ show st.mode

setMode :: Cmd
setMode arg ref = case arg of
  "SmallStep" -> set SmallStep
  "StepTrace" -> set StepTrace
  "BigStep"   -> set BigStep
  "HOAS"      -> set HOAS
  "Closure"   -> set Closure
  other       -> error $ "invalid mode: " <> other
  where
    set :: Mode -> Effect Unit
    set mode = modify_ (\st -> st { mode = mode }) ref

setTiming :: Cmd
setTiming _ = modify_ (\st -> st { timing = true })

showEnv :: Cmd
showEnv _ ref = do
  st <- read ref
  log $ ppState st

typeExpr :: Cmd
typeExpr expr ref = do
  st <- read ref
  case runTyping (inferType expr) (fromState st) of
    Left err -> error $ showTypeError err
    Right output -> do
      log output

loadFile :: Cmd
loadFile file ref = do
  code <- readTextFile file
  evalProg code ref

importFile :: Cmd
importFile file ref = do
  code <- readTextFile file
  st <- read ref
  case runExcept $ runStateT (importDefs code) st of
    Left err -> error $ showTypeError err
    Right (_ /\ st') -> write st' ref

evalProg :: Cmd
evalProg code ref = do
  st <- read ref
  case runExcept $ runStateT (interpret code) st of
    Left err -> error $ showTypeError err
    Right (output /\ st') -> do
      log output
      write st' ref

errorCmd :: Cmd
errorCmd _ ref = do
  error "Invalid input!"
  printHelp "" ref

mayTime :: Cmd -> Cmd
mayTime cmd arg ref = do
  beginTime <- nowTime
  cmd arg ref
  endTime <- nowTime
  st <- read ref
  if st.timing then let seconds = showSeconds $ diff endTime beginTime in
    log $ "(time: " <> seconds <> "s)"
  else pure unit

-- command dispatcher
dispatch :: Cmd
dispatch input = ifMatchesAny (":?" : ":help" : Nil) printHelp $
  ifMatches ":show mode" showMode $
  ifMatches ":set mode" setMode $
  ifMatches ":set timing" setTiming $
  ifMatches ":show env" showEnv $
  ifMatches ":type" (mayTime typeExpr) $
  ifMatches ":load" (mayTime loadFile) $
  ifMatches ":import" (mayTime importFile) $
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

repl :: Effect Unit
repl = do
  log "Next-Gen CP REPL, dev version"
  interface <- createConsoleInterface noCompletion
  setPrompt "> " interface
  prompt interface
  ref <- new initState
  setLineHandler (handler interface ref) interface

-- helpers

readTextFile :: String -> Effect String
readTextFile f = do
  result <- try $ Sync.readTextFile UTF8 f
  case result of Right text -> pure text
                 Left err -> error (withGraphics (foreground Red) (message err)) $> ""

showSeconds :: Milliseconds -> String
showSeconds (Milliseconds n) = show (n / 1000.0) <> "s"
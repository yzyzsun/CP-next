module Main where

import Prelude

import Ansi.Codes (Color(..))
import Ansi.Output (foreground, withGraphics)
import Data.Array.NonEmpty ((!!))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromJust)
import Data.String (Pattern(..), stripPrefix)
import Data.String.Regex (match, replace)
import Data.String.Regex.Flags (global, noFlags)
import Data.String.Regex.Unsafe (unsafeRegex)
import Data.Time (diff)
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.Console (error, log)
import Effect.Exception (Error, message, try)
import Effect.Now (nowTime)
import Node.Encoding (Encoding(..))
import Node.FS.Sync as Sync
import Node.Path (concat, dirname)
import Node.ReadLine (Interface, createConsoleInterface, noCompletion, prompt, setLineHandler, setPrompt)
import Partial.Unsafe (unsafePartial)
import Zord (Mode(..), interpret)

showSeconds :: Milliseconds -> String
showSeconds (Milliseconds n) = show (n / 1000.0) <> "s"

errorRed :: Error -> Effect Unit
errorRed err = error $ withGraphics (foreground Red) (message err)

readTextFile :: String -> Effect String
readTextFile f = do
  result <- try $ Sync.readTextFile UTF8 f
  case result of Right text -> pure text
                 Left err -> errorRed err $> ""

load :: String -> Effect String
load file = do
  let path = dirname file
  program <- readTextFile file
  unsafePartial (preprocess path program)

preprocess :: Partial => String -> String -> Effect String
preprocess path program = case match openRegex program of
  Just arr -> do
    let name = fromJust (fromJust (arr !! 1))
    text <- readTextFile (concat [path, ext name])
    preprocess path $ replace openRegex (replace lineRegex " " text) program
  Nothing -> pure program
  where openRegex = unsafeRegex """open\s+(\w+)\s*;""" noFlags
        lineRegex = unsafeRegex """(--.*)?[\r\n]+""" global
        ext name = name <> ".mzord"

execute :: String -> Mode -> Effect Unit
execute program mode = do
  beginTime <- nowTime
  result <- try $ interpret program mode
  endTime <- nowTime
  let seconds = showSeconds $ diff endTime beginTime
  case result of
    Right output -> log $ output <> "\n<" <> show mode <> " mode: " <> seconds <> ">"
    Left err -> errorRed err

main :: Effect Unit
main = do
  log "Zord REPL, version 0.1.1 (press Ctrl-C to quit)"
  interface <- createConsoleInterface noCompletion
  setPrompt "> " interface
  prompt interface
  flip setLineHandler interface $ handler interface BigStep
  where
    handler :: Interface -> Mode -> String -> Effect Unit
    handler interface mode input = do
      case stripPrefix (Pattern ":mode ") input of
        Just m -> do
          let setMode = flip setLineHandler interface <<< handler interface
          case m of "SmallStep" -> setMode SmallStep
                    "StepTrace" -> setMode StepTrace
                    "BigStep" -> setMode BigStep
                    "HOAS" -> setMode HOAS
                    "Closure" -> setMode Closure
                    _ -> error $ "unknown mode (available: SmallStep StepTrace BigStep HOAS Closure)"
        Nothing -> do
          case stripPrefix (Pattern ":load ") input of
            Just file -> do
              program <- load file
              execute program mode
            Nothing -> execute input mode
      prompt interface

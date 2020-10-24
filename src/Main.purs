module Main where

import Prelude

import Ansi.Codes (Color(..))
import Ansi.Output (foreground, withGraphics)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), stripPrefix)
import Data.Time (diff)
import Data.Time.Duration (Milliseconds(..))
import Effect (Effect)
import Effect.Console (error, log)
import Effect.Exception (Error, message, try)
import Effect.Now (nowTime)
import Node.Encoding (Encoding(..))
import Node.FS.Sync (readTextFile)
import Node.ReadLine (createConsoleInterface, noCompletion, prompt, setLineHandler, setPrompt)
import Zord (Mode(..), interpret)

showSeconds :: Milliseconds -> String
showSeconds (Milliseconds n) = show (n / 1000.0) <> "s"

errorRed :: Error -> Effect Unit
errorRed err = error $ withGraphics (foreground Red) (message err)

execute :: String -> Effect Unit
execute program = do
  beginTime <- nowTime
  result <- try $ interpret Simple program
  endTime <- nowTime
  let seconds = showSeconds $ diff endTime beginTime
  case result of
    Right output -> log $ output <> "\n<Elapsed time: " <> seconds <> ">"
    Left err -> errorRed err

main :: Effect Unit
main = do
  log "Zord REPL, version 0.1.0 (press Ctrl-C to quit)"
  interface <- createConsoleInterface noCompletion
  setPrompt "> " 2 interface
  prompt interface
  setLineHandler interface \input -> do
    case stripPrefix (Pattern ":load ") input of
      Just file -> do result <- try $ readTextFile UTF8 file
                      case result of Right program -> execute program
                                     Left err -> errorRed err
      Nothing -> execute input
    prompt interface

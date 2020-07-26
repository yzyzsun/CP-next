module Main where

import Prelude

import Ansi.Codes (Color(..))
import Ansi.Output (foreground, withGraphics)
import Data.Either (Either(..))
import Effect (Effect)
import Effect.Console (error, log)
import Effect.Exception (message, try)
import Node.Encoding (Encoding(..))
import Node.FS.Sync (readTextFile)
import Node.ReadLine (createConsoleInterface, noCompletion, prompt, setLineHandler, setPrompt)
import Zord (Mode(..), interpret)

main :: Effect Unit
main = do
  log "Zord, version 0.1.0: enter a file path to run source code (press Ctrl-C to quit)"
  interface <- createConsoleInterface noCompletion
  setPrompt ":load " 6 interface
  prompt interface
  setLineHandler interface \f -> do
    result <- try (readTextFile UTF8 f >>= interpret Simple)
    case result of
      Right output -> log output
      Left err -> error $ withGraphics (foreground Red) (message err)
    prompt interface

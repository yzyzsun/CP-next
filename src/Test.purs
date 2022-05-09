module Test.Main where

import Prelude

import Control.Monad.Except (runExcept)
import Control.Monad.State (runStateT)
import Data.Array (filter)
import Data.Array.NonEmpty ((!!))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), codePointFromChar, stripPrefix, takeWhile, trim)
import Data.String.Regex (match, replace)
import Data.String.Regex.Flags (global, noFlags)
import Data.String.Regex.Unsafe (unsafeRegex)
import Data.Traversable (for_)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log, time, timeEnd)
import Effect.Exception (throw)
import Language.CP (interpret, showTypeError)
import Language.CP.Context (initState)
import Language.CP.Util (unsafeFromJust)
import Node.Encoding (Encoding(..))
import Node.FS.Sync (readdir)
import Node.Path (FilePath, concat, extname)
import REPL (readTextFile)
import Node.FS.Aff as Aff
import Test.Spec (it)
import Test.Spec.Assertions (expectError, fail, shouldReturn)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner (runSpec)

testDir :: FilePath
testDir = "examples"

testFiles :: Effect (Array FilePath)
testFiles = do
  files <- readdir testDir
  pure $ filter (\f -> extname f == ".cp") files

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

check :: String -> Effect Unit
check code = case mexpected of
  Just expected -> interpreted `shouldReturn` expected
  Nothing -> case mpassed of
    Just rest -> case stripPrefix (Pattern "Error") rest of
      Just _ -> expectError interpreted
      Nothing -> interpreted $> unit
    Nothing -> fail "no expectation on the first line"
  where mexpected = map trim $ stripPrefix (Pattern "-->") $
                    takeWhile (_ /= codePointFromChar '\n') $ code
        mpassed = trim <$> stripPrefix (Pattern "--|") code
        interpreted = case runExcept $ runStateT (interpret code) initState of
          Left err -> throw $ showTypeError err
          Right (o /\ _) -> pure o

main :: Effect Unit
main = do
  files <- testFiles
  launchAff_ $ runSpec [consoleReporter] do
    for_ files \f -> it f do
      raw <- Aff.readTextFile UTF8 $ concat [testDir, f]
      liftEffect do
        code <- preprocess testDir raw
        newline
        time f
        check code
        timeEnd f
  where newline = log ""

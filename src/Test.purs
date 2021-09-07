module Test.Main where

import Prelude

import Data.Array (filter)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), codePointFromChar, stripPrefix, takeWhile, trim)
import Data.Traversable (for_)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Console (log, time, timeEnd)
import Language.CP (Mode(..), interpret)
import Main (preprocess)
import Node.Encoding (Encoding(..))
import Node.FS.Aff (readTextFile)
import Node.FS.Sync (readdir)
import Node.Path (FilePath, concat, extname)
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
        interpreted = interpret code BigStep

main :: Effect Unit
main = do
  files <- testFiles
  launchAff_ $ runSpec [consoleReporter] do
    for_ files \f -> it f do
      raw <- readTextFile UTF8 $ concat [testDir, f]
      liftEffect do
        code <- preprocess testDir raw
        newline
        time f
        check code
        timeEnd f
  where newline = log ""

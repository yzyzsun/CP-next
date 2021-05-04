module Test.Main where

import Prelude

import Data.Array (filter)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), codePointFromChar, stripPrefix, takeWhile, trim)
import Data.Traversable (for_)
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Main (preprocess)
import Node.Encoding (Encoding(..))
import Node.FS.Aff (readTextFile)
import Node.FS.Sync (readdir)
import Node.Path (FilePath, concat, extname)
import Partial.Unsafe (unsafePartial)
import Test.Spec (describe, it)
import Test.Spec.Assertions (expectError, fail, shouldEqual)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner (runSpec)
import Zord (Mode(..), interpret)

testDir :: FilePath
testDir = "examples"

testFiles :: Effect (Array FilePath)
testFiles = do
  files <- readdir testDir
  pure $ filter (\f -> extname f == ".zord") files

check :: String -> Effect Unit
check code = case mexpected of
  Just expected -> do output <- interpretation
                      expected `shouldEqual` output
  Nothing -> case mpassed of
    Just rest -> case stripPrefix (Pattern "Error") rest of
      Just err -> expectError interpretation
      Nothing -> interpretation $> unit
    Nothing -> fail "no expectation on the first line"
  where mexpected = map trim <<< stripPrefix (Pattern "-->") <<<
                    takeWhile (_ /= codePointFromChar '\n') $ code
        mpassed = trim <$> stripPrefix (Pattern "--|") code
        interpretation = interpret code BigStep

main :: Effect Unit
main = do
  files <- testFiles
  launchAff_ $ runSpec [consoleReporter] do
    describe ("Testing " <> testDir) do
      for_ files \f -> it f do
        raw <- readTextFile UTF8 $ concat [testDir, f]
        code <- liftEffect $ unsafePartial (preprocess testDir raw)
        liftEffect $ check code

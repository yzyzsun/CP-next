module Zord where

import Prelude

import Data.Array ((!!))
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.String (Pattern(..), split)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Exception (throw)
import Text.Parsing.Parser (ParseError(..), runParser)
import Text.Parsing.Parser.Pos (Position(..))
import Text.Parsing.Parser.String (eof)
import Zord.Context (Pos(..), TypeError(..), runTyping)
import Zord.Desugar (desugar)
import Zord.Parser (program, whiteSpace)
import Zord.Semantics.HOAS as HOAS
import Zord.Semantics.NaturalClosure as Closure
import Zord.Semantics.NaturalSubst as BigStep
import Zord.Semantics.StepTrace as StepTrace
import Zord.Semantics.Subst as SmallStep
import Zord.Typing (infer)

data Mode = SmallStep | StepTrace | BigStep | HOAS | Closure

derive instance Generic Mode _
instance Show Mode where show = genericShow

interpret :: String -> Mode -> Effect String
interpret code mode = case runParser code (whiteSpace *> program <* eof) of
  Left err -> throw $ showParseError err code
  Right e -> let e' = desugar e in case runTyping (infer e') of
    Left err -> throw $ showTypeError err
    Right (Tuple e'' _) -> case mode of
      SmallStep -> pure $ show (SmallStep.eval e'')
      StepTrace -> let Tuple _ s = StepTrace.eval e'' in pure $
        show e <> "\n⇣ Desugar\n" <> show e' <> "\n↯ Elaborate\n" <> s ""
      BigStep -> pure $ show (BigStep.eval e'')
      HOAS -> pure $ show (HOAS.eval e'')
      Closure -> pure $ show (Closure.eval e'')

showPosition :: Position -> String
showPosition (Position { line: line, column: column }) =
  show line <> ":" <> show column

showParseError :: ParseError -> String -> String
showParseError (ParseError _ pos@(Position { line: l, column: c })) source =
  showPosition pos <> ": parse error:\n" <>
  case seek l of Just line -> line <> "\n" <> rep (c-1) " " <> "^"
                 Nothing -> ""
  where
    seek :: Int -> Maybe String
    seek line = (split (Pattern "\n") source) !! (line - 1)
    rep :: Int -> String -> String
    rep n s | n <= 0 = ""
            | otherwise = s <> rep (n-1) s

showTypeError :: TypeError -> String
showTypeError (TypeError msg UnknownPos) = msg
showTypeError (TypeError msg (Pos pos expr)) =
  showPosition pos <> ": " <> msg <> "\nin the expression: " <> show expr

module Zord where

import Prelude

import Data.Array ((!!))
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Generic.Rep.Show (genericShow)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split)
import Data.String.CodeUnits (charAt)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Exception (throw)
import Text.Parsing.Parser (ParseError(..), runParser)
import Text.Parsing.Parser.Pos (Position(..))
import Text.Parsing.Parser.String (eof)
import Zord.Context (Pos(..), TypeError(..), runTyping)
import Zord.Desugar (desugar)
import Zord.Parser (program, whiteSpace)
import Zord.Semantics.Natural as Natural
import Zord.Semantics.StepTrace as StepTrace
import Zord.Semantics.Substitution as Substitution
import Zord.Typing (synthesize)

data Mode = SmallStep | BigStep | StepTrace

derive instance genericMode :: Generic Mode _
instance showMode :: Show Mode where show = genericShow

interpret :: String -> Mode -> Effect String
interpret code mode = case runParser code (whiteSpace *> program <* eof) of
  Left err -> throw $ showParseError err code
  Right e -> let e' = desugar e in case runTyping (synthesize e') of
    Left err -> throw $ showTypeError err
    Right (Tuple e'' t) -> case mode of
      SmallStep -> pure $ show (Substitution.eval e'')
      BigStep -> pure $ show (Natural.eval e'')
      StepTrace -> let Tuple _ s = StepTrace.eval e'' in pure $
        show e <> "\n⇣ Desugar\n" <> show e' <> "\n↯ Elaborate\n" <> s ""

seek :: String -> Int -> Int -> Maybe Char
seek str line column = (split (Pattern "\n") str) !! line' >>= charAt column'
  where line' = line - 1
        column' = column - 1

showPosition :: Position -> String
showPosition (Position { line: line, column: column }) =
  show line <> ":" <> show column

showParseError :: ParseError -> String -> String
showParseError (ParseError msg pos) source =
  showPosition pos <> ": parse error" <>
  case sought pos of Just char -> " on input " <> show char
                     Nothing -> ""
  where
    sought :: Position -> Maybe Char
    sought (Position { line: line, column: column }) = seek source line column

showTypeError :: TypeError -> String
showTypeError (TypeError msg UnknownPos) = msg
showTypeError (TypeError msg (Pos pos expr)) =
  showPosition pos <> ": " <> msg <> "\nIn the expression: " <> show expr

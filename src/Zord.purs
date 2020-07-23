module Zord where

import Prelude

import Data.Array ((!!))
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split)
import Data.String.CodeUnits (charAt)
import Effect (Effect)
import Effect.Exception (throw)
import Text.Parsing.Parser (ParseError(..), runParser)
import Text.Parsing.Parser.Pos (Position(..))
import Text.Parsing.Parser.String (eof)
import Zord.Context (Pos(..), TypeError(..), runTyping)
import Zord.Kinding (tyBReduce)
import Zord.Parser (expr)
import Zord.Semantics (eval, tracedEval)
import Zord.Typing (typeOf)

interpret :: Boolean -> String -> Effect String
interpret tracing input = case runParser input (expr <* eof) of
  Left err -> throw $ showParseError err input
  Right e -> case runTyping (tyBReduce <$> typeOf e) of
    Left err -> throw $ showTypeError err
    Right t -> pure $ if tracing then tracedEval e
                      else show (eval e) <> " : " <> show t

seek :: String -> Int -> Int -> Maybe Char
seek str line column = (split (Pattern "\n") str) !! line' >>= charAt column'
  where line' = line - 1
        column' = column - 1

showPosition :: Position -> String
showPosition (Position { line: line, column: column }) =
  show line <> ":" <> show column

showParseError :: ParseError -> String -> String
showParseError (ParseError msg pos) source =
  showPosition pos <> ": parse error" <> (
    case sought pos of Just char -> " on input " <> show char
                       Nothing -> ""
  )
  where
    sought :: Position -> Maybe Char
    sought (Position { line: line, column: column }) = seek source line column

showTypeError :: TypeError -> String
showTypeError (TypeError msg UnknownPos) = msg
showTypeError (TypeError msg (Pos pos expr)) =
  showPosition pos <> ": " <> msg <> "\nIn the expression: " <> show expr

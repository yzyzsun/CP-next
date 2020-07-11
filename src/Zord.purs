module Zord where

import Prelude

import Data.Either (Either(..))
import Data.List (List(..))
import Effect (Effect)
import Effect.Exception (throw)
import Text.Parsing.Parser (ParseError(..), runParser)
import Text.Parsing.Parser.String (eof)
import Zord.Parser (expr)
import Zord.Semantics (eval)
import Zord.Syntax ((<+>))
import Zord.TypeCheck (TypeError(..), typeOf)

interpret :: String -> Effect String
interpret input = case runParser input (expr <* eof) of
  Left (ParseError str pos) -> throw $ str <+> show pos
  Right e -> case typeOf Nil e of
    Left (TypeError str) -> throw str
    Right t -> pure $ show (eval e) <+> ":" <+> show t

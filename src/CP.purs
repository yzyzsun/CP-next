module Language.CP where

import Prelude

import Data.Array ((!!))
import Data.Either (Either(..))
import Data.Generic.Rep (class Generic)
import Data.Maybe (Maybe(..))
import Data.Show.Generic (genericShow)
import Data.String (Pattern(..), split)
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Exception (throw)
import Language.CP.Context (Pos(..), TypeError(..), runTyping)
import Language.CP.Desugar (desugar)
import Language.CP.Parser (program, whiteSpace)
import Language.CP.Semantics.HOAS as HOAS
import Language.CP.Semantics.NaturalClosure as Closure
import Language.CP.Semantics.NaturalSubst as BigStep
import Language.CP.Semantics.StepTrace as StepTrace
import Language.CP.Semantics.Subst as SmallStep
import Language.CP.Syntax.Source (Tm, showDoc)
import Language.CP.Typing (infer)
import Parsing (ParseError(..), Position(..), runParser)
import Parsing.String (eof)

data Mode = SmallStep | StepTrace | BigStep | HOAS | Closure

derive instance Generic Mode _
instance Show Mode where show = genericShow

interpret :: String -> Mode -> Effect String
interpret code mode = case runParser code (whiteSpace *> program <* eof) of
  Left err -> throw $ showParseError err code
  Right e -> let e' = desugar e in case runTyping (infer e') of
    Left err -> throw $ showTypeError err
    Right (e'' /\ _) -> case mode of
      SmallStep -> pure $ show (SmallStep.eval e'')
      StepTrace -> let _ /\ s = StepTrace.eval e'' in pure $
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
showTypeError (TypeError msg (Pos pos expr inDoc)) =
  showPosition pos <> ": " <> msg <> "\nin the expression: " <>
  (if inDoc then showDoc else show) expr

-- Big-step evaluation used after ANTLR parsing
evaluate :: Tm -> Effect String
evaluate e = case runTyping $ infer $ desugar e of
  Left err -> throw $ showTypeError err
  Right (e' /\ _) -> pure $ show (BigStep.eval e')

module Language.CP where

import Prelude

import Control.Monad.State (gets)
import Data.Array ((!!))
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..))
import Data.List (foldl, head, null, takeWhile)
import Data.Maybe (Maybe(..))
import Data.String (Pattern(..), split)
import Data.String.Regex (match, replace)
import Data.String.Regex.Flags (dotAll)
import Data.String.Regex.Unsafe (unsafeRegex)
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Exception (throw)
import Language.CP.CodeGen (fromState, runCodeGen)
import Language.CP.Context (Checking, Mode(..), TmBindings, Typing, REPLState, initState, runChecking, throwCheckError, throwTypeError)
import Language.CP.Desugar (desugar, desugarProg)
import Language.CP.Parser (expr, program, whiteSpace)
import Language.CP.Semantics.HOAS as HOAS
import Language.CP.Semantics.NaturalClosure as Closure
import Language.CP.Semantics.NaturalSubst as BigStep
import Language.CP.Semantics.StepTrace as StepTrace
import Language.CP.Semantics.Subst as SmallStep
import Language.CP.Syntax.Core as C
import Language.CP.Syntax.Source as S
import Language.CP.Typing (checkProg, infer)
import Language.CP.Util (unsafeFromJust)
import Language.JS.Pretty (print)
import Parsing (ParseError(..), Position(..), runParser)
import Parsing.String (eof)

inferType :: String -> Typing String
inferType code = case runParser code (whiteSpace *> expr <* eof) of
  Left err -> throwTypeError $ showParseError err code
  Right e -> do
    _ /\ t <- infer $ desugar e
    pure $ show t

importDefs :: String -> Checking Unit
importDefs code = case runParser code (whiteSpace *> program <* eof) of
  Left err -> throwCheckError $ showParseError err code
  Right prog -> do
    let prog' = desugarProg prog
    _ <- checkProg prog'
    pure unit

wrapUp :: C.Tm -> TmBindings -> C.Tm
wrapUp e b = foldl (#) e $ snd <<< snd <$> b

evalProg :: S.Prog -> Checking String
evalProg prog = do
  let prog'@(S.Prog _ e') = desugarProg prog
  e <- elaborateProg prog'
  mode <- gets (_.mode)
  pure $ case mode of
    SmallStep -> show (SmallStep.eval e)
    StepTrace -> let _ /\ s = StepTrace.eval e in
      show prog <> "\n⇣ Desugar\n" <> show e' <> "\n↯ Elaborate\n" <> s ""
    BigStep -> show (BigStep.eval e)
    HOAS -> show (HOAS.eval e)
    Closure -> show (Closure.eval e)
  where
    elaborateProg p = do
      e /\ _ <- checkProg p
      b <- gets (_.tmBindings)
      pure $ wrapUp e b

-- Source code interpretation used by REPL
interpret :: String -> Checking String
interpret code = case runParser code (whiteSpace *> program <* eof) of
  Left err -> throwCheckError $ showParseError err code
  Right prog -> evalProg prog

-- Big-step evaluation used after ANTLR parsing
evaluate :: S.Prog -> Effect String
evaluate prog = case runChecking (evalProg prog) initState of
  Left err -> throw $ show err
  Right (output /\ _) -> pure output

compile :: String -> REPLState -> Either String (String /\ REPLState)
compile code st = case runParser code (whiteSpace *> program <* eof) of
  Left err -> Left $ showParseError err code
  Right prog -> case runChecking (elaborateProg (desugarProg prog)) st of
    Left err -> Left $ show err
    Right (e /\ st') -> runCodeGen e (fromState st) <#> \s -> (prelude code <> print s) /\ st'
  where
    prelude s = case match preludeRegex s of
      Just arr -> (unsafeFromJust $ unsafeFromJust $ arr NEA.!! 1)
               <> "\n" <> prelude (replace preludeRegex "" s)
      Nothing -> ""
    preludeRegex = unsafeRegex """\{-#\s*PRELUDE\s+(.*?)\s*#-\}""" dotAll
    elaborateProg p = do
      e /\ _ <- checkProg p
      b <- gets (_.tmBindings)
      let diff = if null st.tmBindings then b
                 else let hd = fst <<< unsafeFromJust $ head st.tmBindings in
                      takeWhile (\(x /\ _ /\ _) -> x /= hd) b
      pure $ wrapUp e diff

showParseError :: ParseError -> String -> String
showParseError (ParseError _ pos@(Position { line: l, column: c })) source =
  show pos <> ": parse error:\n" <>
  case seek l of Just line -> line <> "\n" <> rep (c-1) " " <> "^"
                 Nothing -> ""
  where
    seek :: Int -> Maybe String
    seek line = (split (Pattern "\n") source) !! (line - 1)
    rep :: Int -> String -> String
    rep n s | n <= 0 = ""
            | otherwise = s <> rep (n-1) s

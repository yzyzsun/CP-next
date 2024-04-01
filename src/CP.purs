module Language.CP where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.State (gets)
import Data.Array ((!!))
import Data.Array.NonEmpty as NEA
import Data.Bifunctor (lmap, rmap)
import Data.Either (Either(..))
import Data.List (List(..), foldMap, foldl, head, many, null, takeWhile, (:))
import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), split)
import Data.String.Regex (match, replace)
import Data.String.Regex.Flags (dotAll)
import Data.String.Regex.Unsafe (unsafeRegex)
import Data.Tuple (fst, snd)
import Data.Tuple.Nested (type (/\), (/\))
import Effect (Effect)
import Effect.Exception (throw)
import Language.CP.CodeGen (fromState, runCodeGen)
import Language.CP.Context (Checking, Mode(..), REPLState, TmBindings, Typing, emptyCtx, initState, runChecking, runTyping, throwCheckError, throwTypeError)
import Language.CP.Desugar (desugar, desugarProg)
import Language.CP.Parser (SParser, expr, lowerIdentifier, program, symbol, ty, upperIdentifier, whiteSpace)
import Language.CP.Semantics.HOAS as HOAS
import Language.CP.Semantics.NaturalClosure as Closure
import Language.CP.Semantics.NaturalSubst as BigStep
import Language.CP.Semantics.StepTrace as StepTrace
import Language.CP.Semantics.Subst as SmallStep
import Language.CP.Syntax.Common (Name)
import Language.CP.Syntax.Core as C
import Language.CP.Syntax.Source as S
import Language.CP.Transform (translate)
import Language.CP.Typing (checkProg, infer)
import Language.CP.Util (unsafeFromJust)
import Language.JS.Pretty (print)
import Node.Path (FilePath)
import Parsing (ParseError(..), Position(..), fail, runParser)
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
    Elaborate ->
      show prog <> "\n⇣ Desugar\n" <> show e' <> "\n↯ Elaborate\n" <> show e
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

showParseError :: ParseError -> String -> String
showParseError (ParseError _ (Position { line: l, column: c })) source =
  show l <> ":" <> show c <> ": parse error:\n" <>
  case seek l of Just line -> line <> "\n" <> rep (c-1) " " <> "^"
                 Nothing -> ""
  where
    seek :: Int -> Maybe String
    seek line = (split (Pattern "\n") source) !! (line - 1)
    rep :: Int -> String -> String
    rep n s | n <= 0 = ""
            | otherwise = s <> rep (n-1) s


type JSProgram = String
type CPHeader = String

compile :: String -> FilePath -> REPLState -> Either String (JSProgram /\ CPHeader)
compile code f st = case runParser code (whiteSpace *> program <* eof) of
  Left err -> left $ showParseError err code
  Right prog -> case runChecking (elaborateProg (desugarProg prog)) st of
    Left err -> left $ show err
    Right (e /\ st') -> do
      js <- runCodeGen e (fromState st)
      let st'' = initState { tmBindings = takeWhile (\(x /\ _) -> x /= tmHead) st'.tmBindings
                           , tyAliases = takeWhile (\(x /\ _) -> x /= tyHead) st'.tyAliases
                           }
      pure $ (prelude "CP" code <> print js) /\ (prelude "H" code <> serialize st'')
  where
    tmHead = fromMaybe "" $ fst <$> head st.tmBindings
    tyHead = fromMaybe "" $ fst <$> head st.tyAliases
    prelude c s = case match (preludeRegex c) s of
      Just arr -> (unsafeFromJust $ unsafeFromJust $ arr NEA.!! 1)
               <> "\n" <> prelude c (replace (preludeRegex c) "" s)
      Nothing -> ""
    preludeRegex c = unsafeRegex ("""\{-#\s*PRELUDE\s+""" <> c <> """\s+(.*?)\s*#-\}""") dotAll
    elaborateProg p = do
      e /\ _ <- checkProg p
      b <- gets (_.tmBindings)
      let diff = if null st.tmBindings then b
                 else let hd = fst <<< unsafeFromJust $ head st.tmBindings in
                      takeWhile (\(x /\ _ /\ _) -> x /= hd) b
      pure $ wrapUp e diff
    left err = Left $ f <> ": " <> err

serialize :: REPLState -> CPHeader
serialize st = foldMap ppTyAlias st.tyAliases <> foldMap ppTmBinding st.tmBindings
  where
    ppTyAlias (x /\ t) = "type " <> x <> " = " <> show t <> ";\n"
    ppTmBinding (x /\ t /\ _) = "term " <> x <> " : " <> show t <> ";\n"

deserialize :: CPHeader -> Either ParseError REPLState
deserialize s = do
  entries <- runParser s $ many (pTyAlias <|> pTmBinding) <* eof
  let tys /\ tms = discriminate entries
  pure $ initState { tyAliases = tys, tmBindings = tms }
  where
    pTyAlias :: SParser Entry
    pTyAlias = do symbol "type"
                  x <- upperIdentifier
                  symbol "="
                  t <- ty
                  symbol ";"
                  pure $ TyAlias x t
    pTmBinding :: SParser Entry
    pTmBinding = do symbol "term"
                    x <- lowerIdentifier
                    symbol ":"
                    t <- ty
                    symbol ";"
                    t' <- case runTyping (translate t) emptyCtx of
                            Left err -> fail $ show err
                            Right t' -> pure t'
                    pure $ TmBinding x t'
    discriminate :: List Entry -> List (Name /\ S.Ty) /\ List (Name /\ C.Ty /\ (C.Tm -> C.Tm))
    discriminate Nil = Nil /\ Nil
    discriminate (TyAlias x t : entries) = lmap ((x /\ t) : _) (discriminate entries)
    discriminate (TmBinding x t : entries) = rmap ((x /\ t /\ identity) : _) (discriminate entries)

data Entry = TyAlias Name S.Ty | TmBinding Name C.Ty

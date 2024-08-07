module Language.CP.Semantics.HOAS where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Trampoline (Trampoline, runTrampoline)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Semantics.Common (Arg(..), binop, selectLabel, toString, unop)
import Language.CP.Subtyping (isTopLike, split, (<:))
import Language.CP.Syntax.Common (BinOp(..))
import Language.CP.Syntax.Core (Tm(..), Ty(..), alloc, done, read, tmHoas, tyHoas, unfold, write)
import Partial.Unsafe (unsafeCrashWith)

type Eval = Trampoline

eval :: Tm -> Tm
eval = runTrampoline <<< go <<< tmHoas
  where
    go :: Tm -> Eval Tm
    go e@(TmInt _)    = pure e
    go e@(TmDouble _) = pure e
    go e@(TmString _) = pure e
    go e@(TmBool _)   = pure e
    go TmUnit = pure TmUnit
    go TmTop  = pure TmTop
    go (TmUnary op e) = unop op <$> go e
    go (TmBinary op e1 e2) = do
      v1 <- go e1
      v2 <- go e2
      let e = binop op v1 v2
      case op of Index -> go e
                 _   -> pure e
    go (TmIf e1 e2 e3) = do
      v1 <- go e1
      case v1 of
        TmBool true  -> go e2
        TmBool false -> go e3
        _ -> unsafeCrashWith $
          "CP.Semantics.HOAS.eval: impossible if " <> show v1 <> " ..."
    go (TmApp e1 e2 coercive) = do
      v1 <- go e1
      go $ paraApp v1 ((if coercive then TmAnnoArg else TmArg) e2)
    go e@(TmHAbs _ _ _ _) = pure e
    go e@(TmHFix fix _) = go $ fix e
    go (TmAnno e t) = do
      v <- go' e
      case cast v t of
        Just v' -> go v'
        Nothing -> unsafeCrashWith $ "CP.Semantics.HOAS.eval: " <>
                       "impossible casting " <> show v <> " : " <> show t
      where go' :: Tm -> Eval Tm
            go' (TmAnno e' _) = go' e'
            go' e' = go e'
    go (TmMerge e1 e2) = TmMerge <$> go e1 <*> go e2
    go (TmHSwitch e cases) = do
      v <- go e
      match v cases
      where match :: Tm -> List (Ty /\ (Tm -> Tm)) -> Eval Tm
            match v Nil = unsafeCrashWith $ "CP.Semantics.HOAS.eval: " <>
                                            "impossible switch " <> show v <> "..."
            match v ((t /\ f) : cs) = case cast v t of
              Just e' -> go $ f e'
              Nothing -> match v cs
    go (TmRcd l t e) = pure $ TmRcd l t (TmCell (alloc e))
    go (TmPrj e l) = selectLabel <$> go e <@> l >>= go
    go (TmTApp e t) = paraApp <$> go e <@> TyArg t >>= go
    go e@(TmHTAbs _ _ _ _) = pure e
    go (TmFold t e) = TmFold t <$> go e
    go (TmUnfold t e) = if isTopLike t then pure TmTop else go e >>= go'
      where go' :: Tm -> Eval Tm
            go' e'@(TmMerge _ _) = go' <=< go $ TmAnno e' t
            go' (TmFold _ v) = go $ TmAnno v (unfold t)
            go' e' = unsafeCrashWith $ "CP.Semantics.HOAS.eval: " <>
                                       "impossible unfold " <> show e'
    go (TmToString e) = toString <$> go e
    go (TmArray t arr) = pure $ TmArray t (TmCell <<< alloc <$> arr)
    go (TmMain e) = go e >>= force
      where force :: Tm -> Eval Tm
            force (TmMerge v1 v2) = do
              v1' <- force v1
              v2' <- force v2
              pure $ TmMerge v1' v2'
            force (TmRcd l t e') = TmRcd l t <$> go e'
            force (TmArray t arr) = TmArray t <$> traverse go arr
            force v = pure v
    go (TmCell cell) = if done cell then pure e else do
      v <- go e
      pure $ write v cell
      where e = read cell
    go e = unsafeCrashWith $ "CP.Semantics.HOAS.eval: " <>
      "well-typed programs don't get stuck, but got " <> show e

cast :: Tm -> Ty -> Maybe Tm
cast e _ | not (isValue e) = unsafeCrashWith $
  "CP.Semantics.HOAS.cast: " <> show e <> " is not a value"
cast v t | Just (t1 /\ t2) <- split t = TmMerge <$> cast v t1 <*> cast v t2
cast v (TyOr t1 t2) = cast v t1 <|> cast v t2
cast _ t | isTopLike t = Just $ genTopLike t
cast (TmInt i)    TyInt    = Just $ TmInt i
cast (TmDouble n) TyDouble = Just $ TmDouble n
cast (TmString s) TyString = Just $ TmString s
cast (TmBool b)   TyBool   = Just $ TmBool b
cast TmUnit       TyUnit   = Just TmUnit
cast (TmHAbs abs targ1 tret1 _) (TyArrow _ tret2 _)
  | tret1 <: tret2 = Just $ TmHAbs abs targ1 tret2 true
cast (TmMerge v1 v2) t = cast v1 t <|> cast v2 t
cast (TmRcd l t e) (TyRcd l' t')
  | l == l' && t <: t' = Just $ TmRcd l t' e
cast (TmHTAbs tabs td1 tf1 _) (TyForall a td2 t2)
  | td2 <: td1 && tf1 (TyVar a) <: t2
  = Just $ TmHTAbs tabs td1 (tyHoas a t2) true
cast (TmFold t v) t'@(TyRec _ _) | t <: t' = Just $ TmFold t' v
cast (TmArray t arr) (TyArray t') | t <: t' = Just $ TmArray t' arr
cast _ _ = Nothing

paraApp :: Tm -> Arg -> Tm
paraApp (TmHAbs abs _ _ false) (TmArg e) = abs $ TmCell $ alloc e
paraApp (TmHAbs abs _ tret true) (TmArg e) = TmAnno (abs $ TmCell $ alloc e) tret
paraApp (TmHAbs abs targ tret _) (TmAnnoArg e) =
  TmAnno (abs $ TmCell $ alloc $ TmAnno e targ) tret
paraApp (TmHTAbs tabs _ _ false) (TyArg ta) = tabs ta
paraApp (TmHTAbs tabs _ tf true) (TyArg ta) = TmAnno (tabs ta) (tf ta)
paraApp (TmMerge v1 v2) arg = TmMerge (paraApp v1 arg) (paraApp v2 arg)
paraApp v arg = unsafeCrashWith $ "CP.Semantics.HOAS.paraApp: " <>
  "impossible application " <> show v <> " • " <> show arg

genTopLike :: Ty -> Tm
genTopLike TyTop = TmTop
genTopLike (TyArrow _ t _) = TmHAbs (\_ -> TmTop) TyTop t true
genTopLike (TyRcd l t) = TmRcd l t TmTop
genTopLike (TyForall a _ t) = TmHTAbs (\_ -> TmTop) TyTop (tyHoas a t) true
genTopLike (TyRec _ t) = genTopLike t
genTopLike t = unsafeCrashWith $ "CP.Semantics.HOAS.genTopLike: " <>
  "cannot generate a top-like value of type " <> show t

isValue :: Tm -> Boolean
isValue (TmInt _)    = true
isValue (TmDouble _) = true
isValue (TmString _) = true
isValue (TmBool _)   = true
isValue TmUnit       = true
isValue TmTop        = true
isValue (TmHAbs _ _ _ _) = true
isValue (TmMerge e1 e2) = isValue e1 && isValue e2
isValue (TmRcd _ _ _) = true
isValue (TmHTAbs _ _ _ _) = true
isValue (TmFold _ e) = isValue e
isValue (TmArray _ _) = true
isValue _ = false

module Language.CP.Semantics.HOAS where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Trampoline (Trampoline, runTrampoline)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Language.CP.Semantics.Common (Arg(..), binop, selectLabel, toString, unop)
import Language.CP.Subtyping (isTopLike, split, (<:))
import Language.CP.Syntax.Common (BinOp(..))
import Language.CP.Syntax.Core (Tm(..), Ty(..), done, new, read, tmHoas, tyHoas, unfold, write)
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
    go TmUndefined = pure TmUndefined
    go (TmUnary op e) = unop op <$> go e
    go (TmBinary op e1 e2) = do
      e1' <- go e1
      e2' <- go e2
      let e = binop op e1' e2'
      case op of Index -> go e
                 _   -> pure e
    go (TmIf e1 e2 e3) = do
      e1' <- go e1
      case e1' of
        TmBool true  -> go e2
        TmBool false -> go e3
        _ -> unsafeCrashWith $
          "CP.Semantics.HOAS.eval: impossible if " <> show e1' <> " ..."
    go (TmApp e1 e2 coercive) = do
      e1' <- go e1
      go $ paraApp e1' ((if coercive then TmAnnoArg else TmArg) e2)
    go e@(TmHAbs _ _ _ _) = pure e
    go e@(TmHFix fix _) = go $ fix e
    go anno@(TmAnno e t) = do
      e' <- go' e
      case typedReduce e' t of
        Just e'' -> go e''
        Nothing -> unsafeCrashWith $
          "CP.Semantics.HOAS.eval: impossible typed reduction " <> show anno
      where go' :: Tm -> Eval Tm
            go' (TmAnno e' _) = go' e'
            go' e' = go e'
    go (TmMerge e1 e2) = TmMerge <$> go e1 <*> go e2
    go (TmRcd l t e) = pure $ TmRcd l t (TmRef (new e))
    go (TmPrj e l) = selectLabel <$> go e <@> l >>= go
    go (TmTApp e t) = paraApp <$> go e <@> TyArg t >>= go
    go e@(TmHTAbs _ _ _ _) = pure e
    go (TmFold t e) = TmFold t <$> go e
    go (TmUnfold t e) = if isTopLike t then pure TmUnit else go e >>= go'
      where go' :: Tm -> Eval Tm
            go' e'@(TmMerge _ _) = go' <=< go $ TmAnno e' t
            go' (TmFold _ v) = go $ TmAnno v (unfold t)
            go' e' = unsafeCrashWith $ "CP.Semantics.HOAS.eval: " <>
                                       "impossible unfold " <> show e'
    go (TmToString e) = toString <$> go e
    go (TmArray t arr) = pure $ TmArray t (TmRef <<< new <$> arr)
    go (TmRef ref) = if done ref then pure e else do
      e' <- go e
      pure $ write e' ref
      where e = read ref
    go e = unsafeCrashWith $ "CP.Semantics.HOAS.eval: " <>
      "well-typed programs don't get stuck, but got " <> show e

typedReduce :: Tm -> Ty -> Maybe Tm
typedReduce e _ | not (isValue e) = unsafeCrashWith $
  "CP.Semantics.HOAS.typedReduce: " <> show e <> " is not a value"
typedReduce _ t | isTopLike t = Just TmUnit
typedReduce v t | Just (Tuple t1 t2) <- split t = do
  let m1 = isOptionalRcd t1
      m2 = isOptionalRcd t2
      v1 = typedReduce v t1
      v2 = typedReduce v t2
  (TmMerge <$> v1 <*> v2) <|> (m1 *> v2) <|> (m2 *> v1) <|> (m1 *> m2)
  where isOptionalRcd (TyRcd _ _ true) = Just TmUnit
        isOptionalRcd _ = Nothing
typedReduce (TmInt i)    TyInt    = Just $ TmInt i
typedReduce (TmDouble n) TyDouble = Just $ TmDouble n
typedReduce (TmString s) TyString = Just $ TmString s
typedReduce (TmBool b)   TyBool   = Just $ TmBool b
typedReduce (TmHAbs abs targ1 tret1 _) (TyArrow _ tret2 _)
  | tret1 <: tret2 = Just $ TmHAbs abs targ1 tret2 true
typedReduce (TmMerge v1 v2) t = typedReduce v1 t <|> typedReduce v2 t
typedReduce (TmRcd l t e) (TyRcd l' t' _)
  | l == l' && t <: t' = Just $ TmRcd l t' e
typedReduce (TmHTAbs tabs td1 tf1 _) (TyForall a td2 t2)
  | td2 <: td1 && tf1 (TyVar a) <: t2
  = Just $ TmHTAbs tabs td1 (tyHoas a t2) true
typedReduce (TmFold t v) t'@(TyRec _ _) | t <: t' = Just $ TmFold t' v
typedReduce (TmArray t arr) (TyArray t') | t <: t' = Just $ TmArray t' arr
typedReduce _ _ = Nothing

paraApp :: Tm -> Arg -> Tm
paraApp TmUnit _ = TmUnit
paraApp (TmHAbs abs _ _ false) (TmArg e) = abs $ TmRef $ new e
paraApp (TmHAbs abs _ tret true) (TmArg e) = TmAnno (abs $ TmRef $ new e) tret
paraApp (TmHAbs abs targ tret _) (TmAnnoArg e) =
  TmAnno (abs $ TmRef $ new $ TmAnno e targ) tret
paraApp (TmHTAbs tabs _ _ false) (TyArg ta) = tabs ta
paraApp (TmHTAbs tabs _ tf true) (TyArg ta) = TmAnno (tabs ta) (tf ta)
paraApp (TmMerge v1 v2) arg = TmMerge (paraApp v1 arg) (paraApp v2 arg)
paraApp v arg = unsafeCrashWith $ "CP.Semantics.HOAS.paraApp: " <>
  "impossible application " <> show v <> " • " <> show arg

isValue :: Tm -> Boolean
isValue (TmInt _)    = true
isValue (TmDouble _) = true
isValue (TmString _) = true
isValue (TmBool _)   = true
isValue TmUnit       = true
isValue TmUndefined  = true
isValue (TmHAbs _ _ _ _) = true
isValue (TmMerge e1 e2) = isValue e1 && isValue e2
isValue (TmRcd _ _ _) = true
isValue (TmHTAbs _ _ _ _) = true
isValue (TmFold _ e) = isValue e
isValue (TmArray _ _) = true
isValue _ = false

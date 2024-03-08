module Language.CP.Semantics.Closure where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Maybe.Trans (MaybeT, lift, runMaybeT)
import Control.Monad.Reader (ReaderT, ask, local, runReader)
import Control.Plus (empty)
import Data.Array (length, (!!))
import Data.Identity (Identity)
import Data.Map (insert, lookup, union)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Language.CP.Semantics.Common (Arg(..), binop, genTopLike, toString, unop)
import Language.CP.Subtyping (isTopLike, split, (<:))
import Language.CP.Syntax.Common (BinOp(..), Name, UnOp(..), Label)
import Language.CP.Syntax.Core (EvalBind(..), EvalEnv, Tm(..), Ty(..), unfold)
import Language.CP.Util (unsafeFromJust)
import Partial.Unsafe (unsafeCrashWith)

type EvalT :: (Type -> Type) -> Type -> Type
type EvalT = ReaderT EvalEnv

eval :: Tm -> Tm
eval tm = runReader (go tm) Map.empty
  where go :: Tm -> EvalT Identity Tm
        go e | isValue e = pure e
             | otherwise = step e >>= go

step :: forall m. Monad m => Tm -> EvalT m Tm
step (TmUnary op e) | isValue e = pure $ unop' op e
                    | otherwise = TmUnary op <$> step e
step (TmBinary op e1 e2) | isValue e1 && isValue e2 = pure $ binop' op e1 e2
                         | isValue e1 = TmBinary op e1 <$> step e2
                         | otherwise  = TmBinary op <$> step e1 <@> e2
step (TmIf (TmBool true)  e _) = pure e
step (TmIf (TmBool false) _ e) = pure e
step (TmIf e1 e2 e3) = TmIf <$> step e1 <@> e2 <@> e3
step (TmVar x) = ask >>= \env -> case lookup x env of
  Just (TmBind e) -> pure e
  m -> unsafeCrashWith $ "CP.Semantics.Closure.step: " <> x <> " is " <> show m
step (TmApp e1 e2 coercive) | isValue e1 = paraApp e1 <<< arg <$> closure e2
                            where arg = if coercive then TmAnnoArg else TmArg
                            | otherwise = TmApp <$> step e1 <@> e2 <@> coercive
step abs@(TmAbs _ _ _ _ _ _) = closure abs
step fix@(TmFix x e _) = closureWithTmBind x fix e
step (TmAnno (TmAnno e _) t) = pure $ TmAnno e t
step (TmAnno e t) | isValue e = unsafeFromJust <$> (cast e =<< expand t)
                  | otherwise = TmAnno <$> step e <@> t
step (TmMerge e1 e2) | isValue e1 = TmMerge e1 <$> step e2
                     | isValue e2 = TmMerge <$> step e1 <@> e2
                     | otherwise  = TmMerge <$> step e1 <*> step e2
step rcd@(TmRcd _ _ _) = closure rcd
step (TmPrj e l) | isValue e = pure $ selectLabel e l
                 | otherwise = TmPrj <$> step e <@> l
step (TmOptPrj e1 l t e2)
  | isValue e1 = do
      t' <- expand t
      s <- cast e1 (TyRcd l t' false)
      case s of Just e -> pure $ TmPrj e l
                Nothing -> pure e2
  | otherwise = TmOptPrj <$> step e1 <@> l <@> t <@> e2
step (TmTApp e t) | isValue e = paraApp e <<< TyArg <$> expand t
                  | otherwise = TmTApp <$> step e <@> t
step tabs@(TmTAbs _ _ _ _ _) = closure tabs
step (TmDef x e1 e2) = closureWithTmBind x e1 e2
step (TmFold t e) = TmFold t <$> step e
step (TmUnfold t e) | isTopLike t = pure TmTop
                    | TmFold _ e' <- e = pure $ TmAnno e' (unfold t)
                    | TmMerge _ _ <- e = pure $ TmUnfold t (TmAnno e t)
                    | otherwise = TmUnfold t <$> step e
step (TmToString e) | isValue e = pure $ toString e
                    | otherwise = TmToString <$> step e
step arr@(TmArray _ _) = closure arr
step (TmMain e) = step e
step (TmClosure env e) | isValue e = pure e
                       | otherwise = TmClosure env <$> local (const env) (step e)
step e = unsafeCrashWith $ "CP.Semantics.Closure.step: " <>
  "well-typed programs don't get stuck, but got " <> show e

-- the second argument has been expanded in Step-AnnoV
cast :: forall m. Monad m => Tm -> Ty -> EvalT m (Maybe Tm)
cast tm ty = runMaybeT $ go tm ty
  where
    go :: Tm -> Ty -> MaybeT (EvalT m) Tm
    go e _ | not (isValue e) = unsafeCrashWith $
      "CP.Semantics.Closure.cast: " <> show e <> " is not a value"
    go v t | Just (t1 /\ t2) <- split t = do
      let m1 = isOptionalRcd t1
          m2 = isOptionalRcd t2
          v1 = go v t1
          v2 = go v t2
      (TmMerge <$> v1 <*> v2) <|> (m1 *> v2) <|> (m2 *> v1) <|> (m1 *> m2)
      where isOptionalRcd (TyRcd _ _ true) = pure TmTop
            isOptionalRcd _ = empty
    go _ t | isTopLike t = pure $ genTopLike t
    go (TmMerge v1 v2) t = go v1 t <|> go v2 t
    go (TmInt i)    TyInt    = pure $ TmInt i
    go (TmDouble n) TyDouble = pure $ TmDouble n
    go (TmString s) TyString = pure $ TmString s
    go (TmBool b)   TyBool   = pure $ TmBool b
    go TmUnit       TyUnit   = pure TmUnit
    go (TmFold t v) t'@(TyRec _ _) | t <: t' = pure $ TmFold t' v
    go (TmClosure env (TmRcd l1 t1 e)) (TyRcd l2 t2 _) = do
      t1' <- lift $ local (const env) $ expand t1
      if l1 == l2 && t1' <: t2 then pure $ TmClosure env (TmRcd l2 t2 e)
                               else empty
    go (TmClosure env (TmAbs x e targ1 tret1 _ b)) (TyArrow _ tret2 _) = do
      targ1' <- lift $ local (const env) $ expand targ1
      tret1' <- lift $ local (const env) $ expand tret1
      if tret1' <: tret2 then pure $ TmClosure env (TmAbs x e targ1' tret2 true b)
                         else empty
    go (TmClosure env (TmTAbs a1 td1 e t1 _)) (TyForall a2 td2 t2) = do
      td1' <- lift $ local (const env) $ expand td1
      let env' = insert a1 (TyBind Nothing) env
      t1' <- lift $ local (const env') $ expand t1
      -- TODO: a1 can be different from a2
      if a1 == a2 && td2 <: td1' && t1' <: t2
      then pure $ TmClosure env' (TmTAbs a2 td1' e t2 true)
      else empty
    go (TmClosure env (TmArray t1 arr)) (TyArray t2) = do
      t1' <- lift $ local (const env) $ expand t1
      if t1' <: t2 then pure $ TmClosure env (TmArray t2 arr)
                   else empty
    go _ _ = empty

paraApp :: Tm -> Arg -> Tm
paraApp (TmClosure env (TmAbs x e1 _ _ false _)) (TmArg e2) =
  TmClosure (insert x (TmBind e2) env) e1
paraApp (TmClosure env (TmAbs x e1 _ tret true _)) (TmArg e2) =
  TmClosure (insert x (TmBind e2) env) (TmAnno e1 tret)
paraApp (TmClosure env (TmAbs x e1 targ tret _ _)) (TmAnnoArg e2) =
  TmClosure (insert x (TmBind (TmAnno e2 targ)) env) (TmAnno e1 tret)
paraApp (TmClosure env (TmTAbs a _ e _ false)) (TyArg ta) =
  TmClosure (insert a (TyBind (Just ta)) env) e
paraApp (TmClosure env (TmTAbs a _ e t true)) (TyArg ta) =
  TmClosure (insert a (TyBind (Just ta)) env) (TmAnno e t)
paraApp (TmMerge v1 v2) arg = TmMerge (paraApp v1 arg) (paraApp v2 arg)
paraApp v arg = unsafeCrashWith $ "CP.Semantics.Closure.paraApp: " <>
  "impossible application " <> show v <> " • " <> show arg

selectLabel :: Tm -> Label -> Tm
selectLabel (TmMerge e1 e2) l = case selectLabel e1 l, selectLabel e2 l of
  TmTop, TmTop -> TmTop
  TmTop, e2' -> e2'
  e1', TmTop -> e1'
  e1', e2' -> TmMerge e1' e2'
selectLabel (TmClosure env (TmRcd l' t e)) l | l == l' = TmClosure env (TmAnno e t)
selectLabel _ _ = TmTop

unop' :: UnOp -> Tm -> Tm
unop' Len (TmClosure _ (TmArray _ arr)) = TmInt (length arr)
unop' op e = unop op e

binop' :: BinOp -> Tm -> Tm -> Tm
-- TODO: Map union is left-biased so variables in env2 could be shadowed
binop' Append (TmClosure env1 (TmArray t l1)) (TmClosure env2 (TmArray _ l2)) =
  TmClosure (env1 `union` env2) (TmArray t (l1 <> l2))
binop' Index (TmClosure env (TmArray t arr)) (TmInt i) = case arr !! i of
  Just e -> TmClosure env (TmAnno e t)
  Nothing -> unsafeCrashWith $ "CP.Semantics.Closure.binop': the index " <>
    show i <> " is out of bounds for " <> show (TmArray t arr)
binop' op v1 v2 = binop op v1 v2

expand :: forall m. Monad m => Ty -> EvalT m Ty
expand (TyArrow t1 t2 isTrait) = TyArrow <$> expand t1 <*> expand t2 <@> isTrait
expand (TyAnd t1 t2) = TyAnd <$> expand t1 <*> expand t2
expand (TyRcd l t opt) = TyRcd l <$> expand t <@> opt
expand (TyVar a) = ask >>= \env -> case lookup a env of
  Just (TyBind Nothing) -> pure $ TyVar a
  Just (TyBind (Just t)) -> expand t
  m -> unsafeCrashWith $ "CP.Semantics.Closure.expand: " <> a <> " is " <> show m
expand (TyForall a td t) = do
  td' <- expand td
  t' <- local (\env -> insert a (TyBind Nothing) env) (expand t)
  pure $ TyForall a td' t'
expand (TyRec a t) = do
  t' <- local (\env -> insert a (TyBind Nothing) env) (expand t)
  pure $ TyRec a t'
expand (TyArray t) = TyArray <$> expand t
expand t = pure t

isValue :: Tm -> Boolean
isValue (TmInt _)    = true
isValue (TmDouble _) = true
isValue (TmString _) = true
isValue (TmBool _)   = true
isValue TmUnit       = true
isValue TmTop        = true
isValue (TmMerge e1 e2) = isValue e1 && isValue e2
isValue (TmFold _ e) = isValue e
isValue (TmClosure _ (TmRcd _ _ _)) = true
isValue (TmClosure _ (TmAbs _ _ _ _ _ _)) = true
isValue (TmClosure _ (TmTAbs _ _ _ _ _)) = true
isValue (TmClosure _ (TmArray _ _)) = true
isValue _ = false

closure :: forall m. Monad m => Tm -> EvalT m Tm
closure e = ask >>= \env -> pure $ TmClosure env e

closureWithTmBind :: forall m. Monad m => Name -> Tm -> Tm -> EvalT m Tm
closureWithTmBind name tm e = local (\env -> insert name (TmBind tm) env) (closure e)

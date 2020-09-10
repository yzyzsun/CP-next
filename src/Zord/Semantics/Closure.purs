module Zord.Semantics.Closure where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Reader (Reader, ask, local, runReader)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), lookup)
import Partial.Unsafe (unsafeCrashWith)
import Zord.Semantics.Common (binop, selectLabel, toString, unop)
import Zord.Subtyping (isTopLike, split, (<:))
import Zord.Syntax.Common (Name, fromJust)
import Zord.Syntax.Core (EvalBind(..), EvalEnv, Tm(..), Ty(..), tmTSubst, tySubst)

type Eval a = Reader EvalEnv a

eval :: Tm -> Tm
eval tm = runReader (go tm) Nil
  where go :: Tm -> Eval Tm
        go e | isValue e = pure e
             | otherwise  = step e >>= go

step :: Tm -> Eval Tm
step (TmUnary op e) | isValue e = pure $ unop op e
                    | otherwise = TmUnary op <$> step e
step (TmBinary op e1 e2) | isValue e1 && isValue e2 = pure $ binop op e1 e2
                         | isValue e1 = TmBinary op e1 <$> step e2
                         | otherwise  = TmBinary op <$> step e1 <@> e2
step (TmIf (TmBool true)  e2 e3) = pure e2
step (TmIf (TmBool false) e2 e3) = pure e3
step (TmIf e1 e2 e3) = TmIf <$> step e1 <@> e2 <@> e3
step (TmVar x) = ask >>= \env -> case lookup x env of
  Just (TmBind e) -> pure e
  m -> unsafeCrashWith $ "Zord.Semantics.Closure.step: " <> x <> " is " <> show m
step (TmApp e1 e2@(TmClosure _ _)) | isValue e1 = paraApp e1 e2
                                   | otherwise  = TmApp <$> step e1 <@> e2
step (TmApp e1 e2) = TmApp e1 <$> closure e2
step abs@(TmAbs _ _ _ _) = closure abs
step fix@(TmFix x e t) = closureWithTmBind x fix $ TmAnno e t
step (TmAnno (TmAnno e t') t) = pure $ TmAnno e t
step (TmAnno e t) | isValue e = fromJust <$> (expand t >>= typedReduce e)
                  | otherwise  = TmAnno <$> step e <@> t
step (TmMerge e1 e2) | isValue e1 = TmMerge e1 <$> step e2
                     | isValue e2 = TmMerge <$> step e1 <@> e2
                     | otherwise  = TmMerge <$> step e1 <*> step e2
step rcd@(TmRcd _ _ _) = closure rcd
step (TmPrj e l) | isValue e = pure $ selectLabel e l
                 | otherwise = TmPrj <$> step e <@> l
step (TmTApp e t) | isValue e = expand t >>= paraAppTy e
                  | otherwise = TmTApp <$> step e <@> t
step (TmToString e) | isValue e = pure $ toString e
                    | otherwise = TmToString <$> step e
step (TmClosure env e) | isValue e = pure e
                       | otherwise = closureLocal env $ step e
step e = unsafeCrashWith $
  "Zord.Semantics.Closure.step: well-typed programs don't get stuck, but got " <> show e

-- the second argument has been expanded in Step-AnnoV
typedReduce :: Tm -> Ty -> Eval (Maybe Tm)
typedReduce e _ | not (isValue e || isClosureValue e) = unsafeCrashWith $
  "Zord.Semantics.Closure.typedReduce: " <> show e <> " is not a value"
typedReduce _ t | isTopLike t = pure (Just TmUnit)
typedReduce v t | Just (Tuple t1 t2) <- split t = do
  m1 <- typedReduce v t1
  m2 <- typedReduce v t2
  pure (TmMerge <$> m1 <*> m2)
typedReduce (TmInt i)    TyInt    = pure (Just (TmInt i))
typedReduce (TmDouble n) TyDouble = pure (Just (TmDouble n))
typedReduce (TmString s) TyString = pure (Just (TmString s))
typedReduce (TmBool b)   TyBool   = pure (Just (TmBool b))
typedReduce (TmAbs x e targ1 tret1) (TyArr targ2 tret2 _) = do
  targ1' <- expand targ1
  tret1' <- expand tret1
  if targ2 <: targ1' && tret1' <: tret2 then
    pure (Just (TmAbs x e targ1' tret2))
  else pure Nothing
typedReduce (TmMerge v1 v2) t = do
  m1 <- typedReduce v1 t
  m2 <- typedReduce v2 t
  pure (m1 <|> m2)
typedReduce (TmRcd l t e) (TyRcd l' t') = do
  t'' <- expand t
  if l == l' && t'' <: t' then pure (Just (TmRcd l t' (TmAnno e t')))
  else pure Nothing
typedReduce (TmTAbs a1 td1 e t1) (TyForall a2 td2 t2) = do
  td1' <- expand td1
  t1' <- local (Tuple a1 (TyBind Nothing) : _) $ expand t1
  if td2 <: td1' && tySubst a1 (TyVar a2) t1' <: t2 then
    pure (Just (TmTAbs a2 td1' (tmTSubst a1 (TyVar a2) e) t2))
  else pure Nothing
typedReduce (TmClosure env e) t = do
  m <- local (const env) $ typedReduce e t
  pure (TmClosure env <$> m)
typedReduce _ _ = pure Nothing

paraApp :: Tm -> Tm -> Eval Tm
paraApp (TmClosure env v) e = closureLocal env $ paraApp v e
paraApp TmUnit _ = pure TmUnit
paraApp (TmAbs x e1 targ tret) e2 =
  closureWithTmBind x (TmAnno e2 targ) $ TmAnno e1 tret
paraApp (TmMerge v1 v2) e = TmMerge <$> paraApp v1 e <*> paraApp v2 e
paraApp v e = unsafeCrashWith $
  "Zord.Semantics.Closure.paraApp: impossible application of " <> show v <> " to " <> show e

paraAppTy :: Tm -> Ty -> Eval Tm
paraAppTy (TmClosure env v) t = closureLocal env $ paraAppTy v t
paraAppTy TmUnit _ = pure TmUnit
paraAppTy (TmTAbs a _ e t) ta = closureWithTyBind a ta $ TmAnno e t
paraAppTy (TmMerge v1 v2) t = TmMerge <$> paraAppTy v1 t <*> paraAppTy v2 t
paraAppTy v t = unsafeCrashWith $
  "Zord.Semantics.Closure.paraAppTy: impossible application of " <> show v <> " to " <> show t

expand :: Ty -> Eval Ty
expand (TyArr t1 t2 isTrait) = TyArr <$> expand t1 <*> expand t2 <@> isTrait
expand (TyAnd t1 t2) = TyAnd <$> expand t1 <*> expand t2
expand (TyRcd l t) = TyRcd l <$> expand t
expand (TyVar a) = ask >>= \env -> case lookup a env of
  Just (TyBind Nothing) -> pure $ TyVar a
  Just (TyBind (Just t)) -> expand t
  m -> unsafeCrashWith $ "Zord.Semantics.Closure.expand: " <> a <> " is " <> show m
expand (TyForall a td t) = do
  td' <- expand td
  t' <- local (Tuple a (TyBind Nothing) : _) $ expand t
  pure $ TyForall a td' t'
expand t = pure t

isValue :: Tm -> Boolean
isValue (TmInt _)    = true
isValue (TmDouble _) = true
isValue (TmString _) = true
isValue (TmBool _)   = true
isValue (TmUnit)     = true
isValue (TmMerge e1 e2) = isValue e1 && isValue e2
isValue (TmTAbs _ _ _ _) = true
isValue (TmClosure _ e) = isClosureValue e
isValue _ = false

isClosureValue :: Tm -> Boolean
isClosureValue (TmMerge e1 e2) = isClosureValue e1 && isClosureValue e2
isClosureValue (TmAbs _ _ _ _) = true
isClosureValue (TmRcd _ _ _) = true
isClosureValue _ = false

closure :: Tm -> Eval Tm
closure e = ask >>= \env -> pure $ TmClosure env e

closureWithTmBind :: Name -> Tm -> Tm -> Eval Tm
closureWithTmBind name tm e = local (Tuple name (TmBind tm) : _) (closure e)

closureWithTyBind :: Name -> Ty -> Tm -> Eval Tm
closureWithTyBind name ty e = local (Tuple name (TyBind (Just ty)) : _) (closure e)

closureLocal :: EvalEnv -> Eval Tm -> Eval Tm
closureLocal env m = TmClosure env <$> local (const env) m

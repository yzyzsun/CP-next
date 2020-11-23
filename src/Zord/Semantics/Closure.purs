module Zord.Semantics.Closure where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Reader (Reader, ask, local, runReader)
import Data.Array (length, (!!))
import Data.Either (Either(..))
import Data.Map (empty, insert, lookup)
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Semantics.Common (binop, selectLabel, toString, unop)
import Zord.Subtyping (isTopLike, split, (<:))
import Zord.Syntax.Common (BinOp(..), Label, Name, UnOp(..), fromJust)
import Zord.Syntax.Core (EvalBind(..), EvalEnv, Tm(..), Ty(..))

type Eval a = Reader EvalEnv a

eval :: Tm -> Tm
eval tm = runReader (go tm) empty
  where go :: Tm -> Eval Tm
        go e | isValue e = pure e
             | otherwise  = step e >>= go

step :: Tm -> Eval Tm
step (TmUnary op e) | isValue e = pure $ unop' op e
                    | otherwise = TmUnary op <$> step e
step (TmBinary op e1 e2) | isValue e1 && isValue e2 = pure $ binop' op e1 e2
                         | isValue e1 = TmBinary op e1 <$> step e2
                         | otherwise  = TmBinary op <$> step e1 <@> e2
step (TmIf (TmBool true)  e2 e3) = pure e2
step (TmIf (TmBool false) e2 e3) = pure e3
step (TmIf e1 e2 e3) = TmIf <$> step e1 <@> e2 <@> e3
step (TmVar x) = ask >>= \env -> case lookup x env of
  Just (TmBind e) -> pure e
  m -> unsafeCrashWith $ "Zord.Semantics.Closure.step: " <> x <> " is " <> show m
step (TmApp e1 e2) | isValue e1 = paraApp e1 <<< Left <$> closure e2
                   | otherwise  = TmApp <$> step e1 <@> e2
step abs@(TmAbs _ _ _ _) = closure abs
step fix@(TmFix x e t) = closureWithTmBind x fix $ TmAnno e t
step (TmAnno (TmAnno e t') t) = pure $ TmAnno e t
step (TmAnno e t) | isValue e = fromJust <$> (typedReduce e =<< expand t)
                  | otherwise = TmAnno <$> step e <@> t
step (TmMerge e1 e2) | isValue e1 = TmMerge e1 <$> step e2
                     | isValue e2 = TmMerge <$> step e1 <@> e2
                     | otherwise  = TmMerge <$> step e1 <*> step e2
step rcd@(TmRcd _ _ _) = closure rcd
step (TmPrj e l) | isValue e = pure $ selectLabel' e l
                 | otherwise = TmPrj <$> step e <@> l
step (TmTApp e t) | isValue e = paraApp e <<< Right <$> expand t
                  | otherwise = TmTApp <$> step e <@> t
step tabs@(TmTAbs _ _ _ _) = closure tabs
step (TmToString e) | isValue e = pure $ toString e
                    | otherwise = TmToString <$> step e
step (TmClosure env e) | isValue e = pure e
                       | otherwise = TmClosure env <$> local (const env) (step e)
step e = unsafeCrashWith $ "Zord.Semantics.Closure.step: " <>
  "well-typed programs don't get stuck, but got " <> show e

-- the second argument has been expanded in Step-AnnoV
typedReduce :: Tm -> Ty -> Eval (Maybe Tm)
typedReduce e _ | not (isValue e) = unsafeCrashWith $
  "Zord.Semantics.Closure.typedReduce: " <> show e <> " is not a value"
typedReduce _ t | isTopLike t = pure <<< Just $ TmUnit
typedReduce v t | Just (Tuple t1 t2) <- split t = do
  m1 <- typedReduce v t1
  m2 <- typedReduce v t2
  pure $ TmMerge <$> m1 <*> m2
typedReduce (TmMerge v1 v2) t = do
  m1 <- typedReduce v1 t
  m2 <- typedReduce v2 t
  pure $ m1 <|> m2
typedReduce (TmInt i)    TyInt    = pure <<< Just $ TmInt i
typedReduce (TmDouble n) TyDouble = pure <<< Just $ TmDouble n
typedReduce (TmString s) TyString = pure <<< Just $ TmString s
typedReduce (TmBool b)   TyBool   = pure (Just (TmBool b))
typedReduce (TmClosure env (TmRcd l1 t1 e)) (TyRcd l2 t2) = do
  t1' <- local (const env) $ expand t1
  if l1 == l2 && t1' <: t2 then pure <<< Just $ TmClosure env (TmRcd l2 t2 e)
  else pure Nothing
typedReduce (TmClosure env (TmAbs x e targ1 tret1)) (TyArrow targ2 tret2 _) = do
  targ1' <- local (const env) $ expand targ1
  tret1' <- local (const env) $ expand tret1
  if targ2 <: targ1' && tret1' <: tret2 then
    pure <<< Just $ TmClosure env (TmAbs x e targ1' tret2)
  else pure Nothing
typedReduce (TmClosure env (TmTAbs a1 td1 e t1)) (TyForall a2 td2 t2) = do
  td1' <- local (const env) $ expand td1
  let env' = insert a1 (TyBind Nothing) env
  t1' <- local (const env') $ expand t1
  -- TODO: a1 can be different from a2
  if a1 == a2 && td2 <: td1' && t1' <: t2 then
    pure <<< Just $ TmClosure env' (TmTAbs a2 td1' e t2)
  else pure Nothing
typedReduce (TmClosure env (TmArray t1 arr)) (TyArray t2) = do
  t1' <- local (const env) $ expand t1
  if t1' <: t2 then pure <<< Just $ TmClosure env (TmArray t2 arr)
  else pure Nothing
typedReduce _ _ = pure Nothing

paraApp :: Tm -> Either Tm Ty -> Tm
paraApp TmUnit _ = TmUnit
paraApp (TmClosure env (TmAbs x e1 targ tret)) (Left e2) =
  TmClosure (insert x (TmBind (TmAnno e2 targ)) env) (TmAnno e1 tret)
paraApp (TmClosure env (TmTAbs a _ e t)) (Right ta) =
  TmClosure (insert a (TyBind (Just ta)) env) (TmAnno e t)
paraApp (TmMerge v1 v2) et = TmMerge (paraApp v1 et) (paraApp v2 et)
paraApp v e = unsafeCrashWith $ "Zord.Semantics.Closure.paraApp: " <>
  "impossible application " <> show v <> " • " <> show e

selectLabel' :: Tm -> Label -> Tm
selectLabel' (TmClosure env (TmRcd l' t e)) l
  | l == l' = TmClosure env (TmAnno e t)
selectLabel' e l = selectLabel e l

unop' :: UnOp -> Tm -> Tm
unop' Len (TmClosure _ (TmArray _ arr)) = TmInt (length arr)
unop' op e = unop op e

binop' :: BinOp -> Tm -> Tm -> Tm
binop' Append (TmClosure env1 (TmArray t1 l1)) (TmClosure env2 (TmArray t2 l2)) =
  TmClosure (env1 <> env2) (TmArray t1 (l1 <> l2))
binop' Index (TmClosure env (TmArray t arr)) (TmInt i) = case arr !! i of
  Just e -> TmClosure env (TmAnno e t)
  Nothing -> unsafeCrashWith $ "Zord.Semantics.Closure.binop': the index " <>
    show i <> " is out of bounds for " <> show (TmArray t arr)
binop' op v1 v2 = binop op v1 v2

expand :: Ty -> Eval Ty
expand (TyArrow t1 t2 isTrait) = TyArrow <$> expand t1 <*> expand t2 <@> isTrait
expand (TyAnd t1 t2) = TyAnd <$> expand t1 <*> expand t2
expand (TyRcd l t) = TyRcd l <$> expand t
expand (TyVar a) = ask >>= \env -> case lookup a env of
  Just (TyBind Nothing) -> pure $ TyVar a
  Just (TyBind (Just t)) -> expand t
  m -> unsafeCrashWith $ "Zord.Semantics.Closure.expand: " <> a <> " is " <> show m
expand (TyForall a td t) = do
  td' <- expand td
  t' <- local (\env -> insert a (TyBind Nothing) env) (expand t)
  pure $ TyForall a td' t'
expand (TyArray t) = TyArray <$> expand t
expand t = pure t

isValue :: Tm -> Boolean
isValue (TmInt _)    = true
isValue (TmDouble _) = true
isValue (TmString _) = true
isValue (TmBool _)   = true
isValue (TmUnit)     = true
isValue (TmMerge e1 e2) = isValue e1 && isValue e2
isValue (TmClosure _ (TmRcd _ _ _)) = true
isValue (TmClosure _ (TmAbs _ _ _ _)) = true
isValue (TmClosure _ (TmTAbs _ _ _ _)) = true
isValue (TmClosure _ (TmArray _ _)) = true
isValue _ = false

closure :: Tm -> Eval Tm
closure e = ask >>= \env -> pure $ TmClosure env e

closureWithTmBind :: Name -> Tm -> Tm -> Eval Tm
closureWithTmBind name tm e = local (\env -> insert name (TmBind tm) env) (closure e)

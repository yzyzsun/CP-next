module Zord.Semantics where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Reader (Reader, ask, local, runReader)
import Control.Monad.Writer (Writer, runWriter, tell)
import Data.List (List(..), (:))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), lookup)
import Math ((%))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Subtyping (isTopLike, split, (<:))
import Zord.Syntax.Common (ArithOp(..), BinOp(..), CompOp(..), Label, LogicOp(..), Name, UnOp(..), fromJust)
import Zord.Syntax.Core (EvalBind(..), EvalEnv, Tm(..), Ty(..), tmSubst, tmTSubst, tySubst)

----------------------------------------------
-- call-by-name substitution w/ step traces --
----------------------------------------------

type Eval a = Writer String a

computation :: String -> Eval Unit
computation w = tell $ "↓ Step-" <> w <> "\n"

congruence :: String -> Eval Unit
congruence w = tell $ "→ Step-" <> w <> "\n"

eval :: Tm -> Tuple Tm String
eval = go >>> runWriter
  where go :: Tm -> Eval Tm
        go e | isValue e = tell (show e <> "\n") $> e
             | otherwise = tell (show e <> "\n") *> step e >>= go

step :: Tm -> Eval Tm
step (TmUnary op e)
  | isValue e = computation "UnaryV" $> unop op e
  | otherwise = congruence  "Unary"  $> TmUnary op <*> step e
step (TmBinary op e1 e2)
  | isValue e1 && isValue e2 = computation "BinaryV" $> binop op e1 e2
  | isValue e1 = congruence "BinaryR" $> TmBinary op e1 <*> step e2
  | otherwise  = congruence "BinaryL" $> TmBinary op <*> step e1 <@> e2
step (TmIf (TmBool true)  e2 e3) = computation "IfTrue"  $> e2
step (TmIf (TmBool false) e2 e3) = computation "IfFalse" $> e3
step (TmIf e1 e2 e3) = congruence "If" $> TmIf <*> step e1 <@> e2 <@> e3
step (TmApp e1 e2)
  | isValue e1 = computation "PApp" $> paraApp e1 e2
  | otherwise  = congruence  "AppL" $> TmApp <*> step e1 <@> e2
step (TmFix x e t) = computation "Fix" $> TmAnno (tmSubst x (TmFix x e t) e) t
step (TmAnno (TmAnno e t') t) = computation "AnnoAnno" $> TmAnno e t
step (TmAnno e t)
  | isValue e = computation "AnnoV" $> fromJust (typedReduce e t)
  | otherwise = congruence  "Anno"  $> TmAnno <*> step e <@> t
step (TmMerge e1 e2)
  | isValue e1 = congruence "MergeR" $> TmMerge e1 <*> step e2
  | isValue e2 = congruence "MergeL" $> TmMerge <*> step e1 <@> e2
  | otherwise  = congruence "Merge"  $> TmMerge <*> step e1 <*> step e2
step (TmPrj e l)
  | isValue e = computation "PProj" $> selectLabel e l
  | otherwise = congruence  "Proj"  $> TmPrj <*> step e <@> l
step (TmTApp e t)
  | isValue e = computation "PTApp" $> paraAppTy e t
  | otherwise = congruence  "TApp"  $> TmTApp <*> step e <@> t
step (TmToString e)
  | isValue e = computation "ToStringV" $> toString e
  | otherwise = congruence  "ToString"  $> TmToString <*> step e
step e = unsafeCrashWith $
  "Zord.Semantics.step: well-typed programs don't get stuck, but got " <> show e

typedReduce :: Tm -> Ty -> Maybe Tm
typedReduce e _ | not (isValue e) = unsafeCrashWith $
  "Zord.Semantics.typedReduce: " <> show e <> " is not a value"
typedReduce _ t | isTopLike t = Just TmUnit
typedReduce v t | Just (Tuple t1 t2) <- split t = do
  v1 <- typedReduce v t1
  v2 <- typedReduce v t2
  Just $ TmMerge v1 v2
typedReduce (TmInt i)    TyInt    = Just $ TmInt i
typedReduce (TmDouble n) TyDouble = Just $ TmDouble n
typedReduce (TmString s) TyString = Just $ TmString s
typedReduce (TmBool b)   TyBool   = Just $ TmBool b
typedReduce (TmAbs x e targ1 tret1) (TyArr targ2 tret2 _)
  | targ2 <: targ1 && tret1 <: tret2 = Just $ TmAbs x e targ1 tret2
typedReduce (TmMerge v1 v2) t = typedReduce v1 t <|> typedReduce v2 t
typedReduce (TmRcd l t e) (TyRcd l' t')
  | l == l' && t <: t' = Just $ TmRcd l t' (TmAnno e t')
typedReduce (TmTAbs a1 td1 e t1) (TyForall a2 td2 t2)
  | td2 <: td1 && tySubst a1 (TyVar a2) t1 <: t2
  = Just $ TmTAbs a2 td1 (tmTSubst a1 (TyVar a2) e) t2
typedReduce _ _ = Nothing

paraApp :: Tm -> Tm -> Tm
paraApp TmUnit _ = TmUnit
paraApp (TmAbs x e1 targ tret) e2 = TmAnno (tmSubst x (TmAnno e2 targ) e1) tret
paraApp (TmMerge v1 v2) e = TmMerge (paraApp v1 e) (paraApp v2 e)
paraApp v e = unsafeCrashWith $
  "Zord.Semantics.paraApp: impossible application of " <> show v <> " to " <> show e

paraAppTy :: Tm -> Ty -> Tm
paraAppTy TmUnit _ = TmUnit
paraAppTy (TmTAbs a _ e t) ta = TmAnno (tmTSubst a ta e) (tySubst a ta t)
paraAppTy (TmMerge v1 v2) t = TmMerge (paraAppTy v1 t) (paraAppTy v2 t)
paraAppTy v t = unsafeCrashWith $
  "Zord.Semantics.paraAppTy: impossible application of " <> show v <> " to " <> show t

isValue :: Tm -> Boolean
isValue (TmInt _)    = true
isValue (TmDouble _) = true
isValue (TmString _) = true
isValue (TmBool _)   = true
isValue (TmUnit)     = true
isValue (TmAbs _ _ _ _) = true
isValue (TmMerge e1 e2) = isValue e1 && isValue e2
isValue (TmRcd _ _ _) = true
isValue (TmTAbs _ _ _ _) = true
isValue _ = false

---------------------------
-- call-by-name closures --
---------------------------

type Eval' a = Reader EvalEnv a

eval' :: Tm -> Tm
eval' tm = runReader (go tm) Nil
  where go :: Tm -> Eval' Tm
        go e | isValue' e = pure e
             | otherwise  = step' e >>= go

step' :: Tm -> Eval' Tm
step' (TmUnary op e) | isValue' e = pure $ unop op e
                     | otherwise  = TmUnary op <$> step' e
step' (TmBinary op e1 e2) | isValue' e1 && isValue' e2 = pure $ binop op e1 e2
                          | isValue' e1 = TmBinary op e1 <$> step' e2
                          | otherwise   = TmBinary op <$> step' e1 <@> e2
step' (TmIf (TmBool true)  e2 e3) = pure e2
step' (TmIf (TmBool false) e2 e3) = pure e3
step' (TmIf e1 e2 e3) = TmIf <$> step' e1 <@> e2 <@> e3
step' (TmVar x) = ask >>= \env -> case lookup x env of
  Just (TmBind e) -> pure e
  m -> unsafeCrashWith $ "Zord.Semantics.step': " <> x <> " is " <> show m
step' (TmApp e1 e2@(TmClosure _ _)) | isValue' e1 = paraApp' e1 e2
                                    | otherwise   = TmApp <$> step' e1 <@> e2
step' (TmApp e1 e2) = TmApp e1 <$> closure e2
step' abs@(TmAbs _ _ _ _) = closure abs
step' fix@(TmFix x e t) = closureWithTmBind x fix $ TmAnno e t
step' (TmAnno (TmAnno e t') t) = pure $ TmAnno e t
step' (TmAnno e t) | isValue' e = fromJust <$> (expand t >>= typedReduce' e)
                   | otherwise  = TmAnno <$> step' e <@> t
step' (TmMerge e1 e2) | isValue' e1 = TmMerge e1 <$> step' e2
                      | isValue' e2 = TmMerge <$> step' e1 <@> e2
                      | otherwise   = TmMerge <$> step' e1 <*> step' e2
step' rcd@(TmRcd _ _ _) = closure rcd
step' (TmPrj e l) | isValue' e = pure $ selectLabel e l
                  | otherwise  = TmPrj <$> step' e <@> l
step' (TmTApp e t) | isValue' e = expand t >>= paraAppTy' e
                   | otherwise  = TmTApp <$> step' e <@> t
step' (TmToString e) | isValue' e = pure $ toString e
                     | otherwise  = TmToString <$> step' e
step' (TmClosure env e) | isValue' e = pure e
                        | otherwise  = closureLocal env $ step' e
step' e = unsafeCrashWith $
  "Zord.Semantics.step': well-typed programs don't get stuck, but got " <> show e

-- the second argument has been expanded in Step-AnnoV
typedReduce' :: Tm -> Ty -> Eval' (Maybe Tm)
typedReduce' e _ | not (isValue' e || isClosureValue e) = unsafeCrashWith $
  "Zord.Semantics.typedReduce': " <> show e <> " is not a value"
typedReduce' _ t | isTopLike t = pure (Just TmUnit)
typedReduce' v t | Just (Tuple t1 t2) <- split t = do
  m1 <- typedReduce' v t1
  m2 <- typedReduce' v t2
  pure (TmMerge <$> m1 <*> m2)
typedReduce' (TmInt i)    TyInt    = pure (Just (TmInt i))
typedReduce' (TmDouble n) TyDouble = pure (Just (TmDouble n))
typedReduce' (TmString s) TyString = pure (Just (TmString s))
typedReduce' (TmBool b)   TyBool   = pure (Just (TmBool b))
typedReduce' (TmAbs x e targ1 tret1) (TyArr targ2 tret2 _) = do
  targ1' <- expand targ1
  tret1' <- expand tret1
  if targ2 <: targ1' && tret1' <: tret2 then
    pure (Just (TmAbs x e targ1' tret2))
  else pure Nothing
typedReduce' (TmMerge v1 v2) t = do
  m1 <- typedReduce' v1 t
  m2 <- typedReduce' v2 t
  pure (m1 <|> m2)
typedReduce' (TmRcd l t e) (TyRcd l' t') = do
  t'' <- expand t
  if l == l' && t'' <: t' then pure (Just (TmRcd l t' (TmAnno e t')))
  else pure Nothing
typedReduce' (TmTAbs a1 td1 e t1) (TyForall a2 td2 t2) = do
  td1' <- expand td1
  t1' <- local (Tuple a1 (TyBind Nothing) : _) $ expand t1
  if td2 <: td1' && tySubst a1 (TyVar a2) t1' <: t2 then
    pure (Just (TmTAbs a2 td1' (tmTSubst a1 (TyVar a2) e) t2))
  else pure Nothing
typedReduce' (TmClosure env e) t = do
  m <- local (const env) $ typedReduce' e t
  pure (TmClosure env <$> m)
typedReduce' _ _ = pure Nothing

paraApp' :: Tm -> Tm -> Eval' Tm
paraApp' (TmClosure env v) e = closureLocal env $ paraApp' v e
paraApp' TmUnit _ = pure TmUnit
paraApp' (TmAbs x e1 targ tret) e2 =
  closureWithTmBind x (TmAnno e2 targ) $ TmAnno e1 tret
paraApp' (TmMerge v1 v2) e = TmMerge <$> paraApp' v1 e <*> paraApp' v2 e
paraApp' v e = unsafeCrashWith $
  "Zord.Semantics.paraApp': impossible application of " <> show v <> " to " <> show e

paraAppTy' :: Tm -> Ty -> Eval' Tm
paraAppTy' (TmClosure env v) t = closureLocal env $ paraAppTy' v t
paraAppTy' TmUnit _ = pure TmUnit
paraAppTy' (TmTAbs a _ e t) ta = closureWithTyBind a ta $ TmAnno e t
paraAppTy' (TmMerge v1 v2) t = TmMerge <$> paraAppTy' v1 t <*> paraAppTy' v2 t
paraAppTy' v t = unsafeCrashWith $
  "Zord.Semantics.paraAppTy': impossible application of " <> show v <> " to " <> show t

expand :: Ty -> Eval' Ty
expand (TyArr t1 t2 isTrait) = TyArr <$> expand t1 <*> expand t2 <@> isTrait
expand (TyAnd t1 t2) = TyAnd <$> expand t1 <*> expand t2
expand (TyRcd l t) = TyRcd l <$> expand t
expand (TyVar a) = ask >>= \env -> case lookup a env of
  Just (TyBind Nothing) -> pure $ TyVar a
  Just (TyBind (Just t)) -> expand t
  m -> unsafeCrashWith $ "Zord.Semantics.expand: " <> a <> " is " <> show m
expand (TyForall a td t) = do
  td' <- expand td
  t' <- local (Tuple a (TyBind Nothing) : _) $ expand t
  pure $ TyForall a td' t'
expand t = pure t

isValue' :: Tm -> Boolean
isValue' (TmInt _)    = true
isValue' (TmDouble _) = true
isValue' (TmString _) = true
isValue' (TmBool _)   = true
isValue' (TmUnit)     = true
isValue' (TmMerge e1 e2) = isValue' e1 && isValue' e2
isValue' (TmTAbs _ _ _ _) = true
isValue' (TmClosure _ e) = isClosureValue e
isValue' _ = false

isClosureValue :: Tm -> Boolean
isClosureValue (TmMerge e1 e2) = isClosureValue e1 && isClosureValue e2
isClosureValue (TmAbs _ _ _ _) = true
isClosureValue (TmRcd _ _ _) = true
isClosureValue _ = false

closure :: Tm -> Eval' Tm
closure e = ask >>= \env -> pure $ TmClosure env e

closureWithTmBind :: Name -> Tm -> Tm -> Eval' Tm
closureWithTmBind name tm e = local (Tuple name (TmBind tm) : _) (closure e)

closureWithTyBind :: Name -> Ty -> Tm -> Eval' Tm
closureWithTyBind name ty e = local (Tuple name (TyBind (Just ty)) : _) (closure e)

closureLocal :: EvalEnv -> Eval' Tm -> Eval' Tm
closureLocal env m = TmClosure env <$> local (const env) m

-----------------------
-- common operations --
-----------------------

unop :: UnOp -> Tm -> Tm
unop Neg (TmInt i)    = TmInt    (negate i)
unop Neg (TmDouble n) = TmDouble (negate n)
unop Not (TmBool b)   = TmBool   (not b)
unop op v = unsafeCrashWith $
  "Zord.Semantics.binop: impossible unary operation " <> show op <> " on " <> show v

binop :: BinOp -> Tm -> Tm -> Tm
binop (Arith Add) (TmInt i1) (TmInt i2) = TmInt (i1 + i2)
binop (Arith Sub) (TmInt i1) (TmInt i2) = TmInt (i1 - i2)
binop (Arith Mul) (TmInt i1) (TmInt i2) = TmInt (i1 * i2)
binop (Arith Div) (TmInt i1) (TmInt i2) = TmInt (i1 / i2)
binop (Arith Mod) (TmInt i1) (TmInt i2) = TmInt (i1 `mod` i2)
binop (Arith Add) (TmDouble n1) (TmDouble n2) = TmDouble (n1 + n2)
binop (Arith Sub) (TmDouble n1) (TmDouble n2) = TmDouble (n1 - n2)
binop (Arith Mul) (TmDouble n1) (TmDouble n2) = TmDouble (n1 * n2)
binop (Arith Div) (TmDouble n1) (TmDouble n2) = TmDouble (n1 / n2)
binop (Arith Mod) (TmDouble n1) (TmDouble n2) = TmDouble (n1 % n2)
binop (Comp Eql) (TmInt i1) (TmInt i2) = TmBool (i1 == i2)
binop (Comp Neq) (TmInt i1) (TmInt i2) = TmBool (i1 /= i2)
binop (Comp Lt ) (TmInt i1) (TmInt i2) = TmBool (i1 <  i2)
binop (Comp Le ) (TmInt i1) (TmInt i2) = TmBool (i1 <= i2)
binop (Comp Gt ) (TmInt i1) (TmInt i2) = TmBool (i1 >  i2)
binop (Comp Ge ) (TmInt i1) (TmInt i2) = TmBool (i1 >= i2)
binop (Comp Eql) (TmDouble n1) (TmDouble n2) = TmBool (n1 == n2)
binop (Comp Neq) (TmDouble n1) (TmDouble n2) = TmBool (n1 /= n2)
binop (Comp Lt ) (TmDouble n1) (TmDouble n2) = TmBool (n1 <  n2)
binop (Comp Le ) (TmDouble n1) (TmDouble n2) = TmBool (n1 <= n2)
binop (Comp Gt ) (TmDouble n1) (TmDouble n2) = TmBool (n1 >  n2)
binop (Comp Ge ) (TmDouble n1) (TmDouble n2) = TmBool (n1 >= n2)
binop (Comp Eql) (TmString s1) (TmString s2) = TmBool (s1 == s2)
binop (Comp Neq) (TmString s1) (TmString s2) = TmBool (s1 /= s2)
binop (Comp Lt ) (TmString s1) (TmString s2) = TmBool (s1 <  s2)
binop (Comp Le ) (TmString s1) (TmString s2) = TmBool (s1 <= s2)
binop (Comp Gt ) (TmString s1) (TmString s2) = TmBool (s1 >  s2)
binop (Comp Ge ) (TmString s1) (TmString s2) = TmBool (s1 >= s2)
binop (Comp Eql) (TmBool b1) (TmBool b2) = TmBool (b1 == b2)
binop (Comp Neq) (TmBool b1) (TmBool b2) = TmBool (b1 /= b2)
binop (Comp Lt ) (TmBool b1) (TmBool b2) = TmBool (b1 <  b2)
binop (Comp Le ) (TmBool b1) (TmBool b2) = TmBool (b1 <= b2)
binop (Comp Gt ) (TmBool b1) (TmBool b2) = TmBool (b1 >  b2)
binop (Comp Ge ) (TmBool b1) (TmBool b2) = TmBool (b1 >= b2)
binop (Logic And) (TmBool b1) (TmBool b2) = TmBool (b1 && b2)
binop (Logic Or ) (TmBool b1) (TmBool b2) = TmBool (b1 || b2)
binop Append (TmString s1) (TmString s2) = TmString (s1 <> s2)
binop op v1 v2 = unsafeCrashWith $
  "Zord.Semantics.binop: impossible binary operation " <> show op <>
  " between " <> show v1 <> " and " <> show v2

toString :: Tm -> Tm
toString (TmInt i)    = TmString (show i)
toString (TmDouble n) = TmString (show n)
toString (TmString s) = TmString (show s)
toString (TmBool b)   = TmString (show b)
toString v = unsafeCrashWith $
  "Zord.Semantics.toString: impossible from " <> show v <> " to string"

selectLabel :: Tm -> Label -> Tm
selectLabel (TmMerge e1 e2) l = case selectLabel e1 l, selectLabel e2 l of
  TmUnit, TmUnit -> TmUnit
  TmUnit, e2' -> e2'
  e1', TmUnit -> e1'
  e1', e2' -> TmMerge e1' e2'
selectLabel (TmRcd l' _ e) l | l == l' = e
selectLabel (TmClosure env e) l = case selectLabel e l of
  TmUnit -> TmUnit
  e' -> TmClosure env e'
selectLabel _ _ = TmUnit

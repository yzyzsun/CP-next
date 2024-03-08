module Language.CP.Semantics.Common where

import Prelude

import Data.Array (length, (!!))
import Data.Maybe (Maybe(..))
import Data.Number (sqrt, (%))
import Language.CP.Syntax.Common (ArithOp(..), BinOp(..), CompOp(..), Label, LogicOp(..), UnOp(..))
import Language.CP.Syntax.Core (Tm(..), Ty(..))
import Partial.Unsafe (unsafeCrashWith)

unop :: UnOp -> Tm -> Tm
unop Neg  (TmInt i)       = TmInt    (negate i)
unop Neg  (TmDouble n)    = TmDouble (negate n)
unop Len  (TmArray _ arr) = TmInt    (length arr)
unop Sqrt (TmDouble n)    = TmDouble (sqrt n)
unop op v = unsafeCrashWith $
  "CP.Semantics.Common.unop: impossible unary operation " <> show op <>
  " on " <> show v

binop :: BinOp -> Tm -> Tm -> Tm
binop (Arith op) v1 v2 = arith op v1 v2
binop (Comp  op) v1 v2 = comp  op v1 v2
binop (Logic op) v1 v2 = logic op v1 v2
binop Append (TmString s1)  (TmString s2)  = TmString (s1 <> s2)
binop Append (TmArray t l1) (TmArray _ l2) = TmArray t (l1 <> l2)
binop Index (TmArray t arr) (TmInt i) = case arr !! i of
  Just e -> TmAnno e t
  Nothing -> unsafeCrashWith $ "CP.Semantics.Common.binop: the index " <>
    show i <> " is out of bounds for " <> show (TmArray t arr)
binop op v1 v2 = unsafeCrashWithBinop op v1 v2

arith :: ArithOp -> Tm -> Tm -> Tm
arith Add (TmInt i1) (TmInt i2) = TmInt (i1 + i2)
arith Sub (TmInt i1) (TmInt i2) = TmInt (i1 - i2)
arith Mul (TmInt i1) (TmInt i2) = TmInt (i1 * i2)
arith Div (TmInt i1) (TmInt i2) = TmInt (i1 / i2)
arith Mod (TmInt i1) (TmInt i2) = TmInt (i1 `mod` i2)
arith Add (TmDouble n1) (TmDouble n2) = TmDouble (n1 + n2)
arith Sub (TmDouble n1) (TmDouble n2) = TmDouble (n1 - n2)
arith Mul (TmDouble n1) (TmDouble n2) = TmDouble (n1 * n2)
arith Div (TmDouble n1) (TmDouble n2) = TmDouble (n1 / n2)
arith Mod (TmDouble n1) (TmDouble n2) = TmDouble (n1 % n2)
arith op v1 v2 = unsafeCrashWithBinop (Arith op) v1 v2

comp :: CompOp -> Tm -> Tm -> Tm
comp Eql (TmInt i1) (TmInt i2) = TmBool (i1 == i2)
comp Neq (TmInt i1) (TmInt i2) = TmBool (i1 /= i2)
comp Lt  (TmInt i1) (TmInt i2) = TmBool (i1 <  i2)
comp Le  (TmInt i1) (TmInt i2) = TmBool (i1 <= i2)
comp Gt  (TmInt i1) (TmInt i2) = TmBool (i1 >  i2)
comp Ge  (TmInt i1) (TmInt i2) = TmBool (i1 >= i2)
comp Eql (TmDouble n1) (TmDouble n2) = TmBool (n1 == n2)
comp Neq (TmDouble n1) (TmDouble n2) = TmBool (n1 /= n2)
comp Lt  (TmDouble n1) (TmDouble n2) = TmBool (n1 <  n2)
comp Le  (TmDouble n1) (TmDouble n2) = TmBool (n1 <= n2)
comp Gt  (TmDouble n1) (TmDouble n2) = TmBool (n1 >  n2)
comp Ge  (TmDouble n1) (TmDouble n2) = TmBool (n1 >= n2)
comp Eql (TmString s1) (TmString s2) = TmBool (s1 == s2)
comp Neq (TmString s1) (TmString s2) = TmBool (s1 /= s2)
comp Lt  (TmString s1) (TmString s2) = TmBool (s1 <  s2)
comp Le  (TmString s1) (TmString s2) = TmBool (s1 <= s2)
comp Gt  (TmString s1) (TmString s2) = TmBool (s1 >  s2)
comp Ge  (TmString s1) (TmString s2) = TmBool (s1 >= s2)
comp Eql (TmBool b1) (TmBool b2) = TmBool (b1 == b2)
comp Neq (TmBool b1) (TmBool b2) = TmBool (b1 /= b2)
comp Lt  (TmBool b1) (TmBool b2) = TmBool (b1 <  b2)
comp Le  (TmBool b1) (TmBool b2) = TmBool (b1 <= b2)
comp Gt  (TmBool b1) (TmBool b2) = TmBool (b1 >  b2)
comp Ge  (TmBool b1) (TmBool b2) = TmBool (b1 >= b2)
comp op v1 v2 = unsafeCrashWithBinop (Comp op) v1 v2

logic :: LogicOp -> Tm -> Tm -> Tm
logic And (TmBool b1) (TmBool b2) = TmBool (b1 && b2)
logic Or  (TmBool b1) (TmBool b2) = TmBool (b1 || b2)
logic op v1 v2 = unsafeCrashWithBinop (Logic op) v1 v2

unsafeCrashWithBinop :: forall a. BinOp -> Tm -> Tm -> a
unsafeCrashWithBinop op v1 v2 = unsafeCrashWith $
  "CP.Semantics.Common.binop: impossible binary operation " <> show op <>
  " between " <> show v1 <> " and " <> show v2

toString :: Tm -> Tm
toString s@(TmString _) = s
toString (TmInt i)    = TmString (show i)
toString (TmDouble n) = TmString (show n)
toString (TmBool b)   = TmString (show b)
toString v = unsafeCrashWith $
  "CP.Semantics.Common.toString: impossible from " <> show v <> " to string"

selectLabel :: Tm -> Label -> Tm
selectLabel (TmMerge e1 e2) l = case selectLabel e1 l, selectLabel e2 l of
  TmTop, TmTop -> TmTop
  TmTop, e2' -> e2'
  e1', TmTop -> e1'
  e1', e2' -> TmMerge e1' e2'
selectLabel (TmRcd l' t e) l | l == l' = TmAnno e t
selectLabel _ _ = TmTop

genTopLike :: Ty -> Tm
genTopLike TyTop = TmTop
genTopLike (TyArrow _ t b) = TmAbs "$top" TmTop TyTop t true b
genTopLike (TyRcd l t _) = TmRcd l t TmTop
genTopLike (TyForall a _ t) = TmTAbs a TyTop TmTop t true
genTopLike (TyRec _ t) = genTopLike t
genTopLike t = unsafeCrashWith $ "CP.Semantics.Common.genTopLike: " <>
  "cannot generate a top-like value of type " <> show t

data Arg = TmArg Tm | TmAnnoArg Tm | TyArg Ty

instance Show Arg where
  show (TmArg tm) = show tm
  show (TmAnnoArg tm) = show tm
  show (TyArg ty) = show ty

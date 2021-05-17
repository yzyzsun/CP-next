module Zord.Semantics.Common where

import Prelude

import Data.Array (length, (!!))
import Data.Maybe (Maybe(..))
import Math ((%))
import Partial.Unsafe (unsafeCrashWith)
import Zord.Syntax.Common (ArithOp(..), BinOp(..), CompOp(..), Label, LogicOp(..), UnOp(..))
import Zord.Syntax.Core (Tm(..))

unop :: UnOp -> Tm -> Tm
unop Neg (TmInt i)       = TmInt    (negate i)
unop Neg (TmDouble n)    = TmDouble (negate n)
unop Not (TmBool b)      = TmBool   (not b)
unop Len (TmArray _ arr) = TmInt    (length arr)
unop op v = unsafeCrashWith $
  "Zord.Semantics.Common.unop: impossible unary operation " <> show op <>
  " on " <> show v

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
binop Append (TmArray t l1) (TmArray _ l2) = TmArray t (l1 <> l2)
binop Index (TmArray t arr) (TmInt i) = case arr !! i of
  Just e -> TmAnno e t
  Nothing -> unsafeCrashWith $ "Zord.Semantics.Common.binop: the index " <>
    show i <> " is out of bounds for " <> show (TmArray t arr)
binop op v1 v2 = unsafeCrashWith $
  "Zord.Semantics.Common.binop: impossible binary operation " <> show op <>
  " between " <> show v1 <> " and " <> show v2

toString :: Tm -> Tm
toString (TmInt i)    = TmString (show i)
toString (TmDouble n) = TmString (show n)
toString (TmString s) = TmString (show s)
toString (TmBool b)   = TmString (show b)
toString v = unsafeCrashWith $
  "Zord.Semantics.Common.toString: impossible from " <> show v <> " to string"

selectLabel :: Tm -> Label -> Tm
selectLabel (TmMerge e1 e2) l = case selectLabel e1 l, selectLabel e2 l of
  TmUnit, TmUnit -> TmUnit
  TmUnit, e2' -> e2'
  e1', TmUnit -> e1'
  e1', e2' -> TmMerge e1' e2'
selectLabel (TmRcd l' t e) l | l == l' = TmAnno e t
selectLabel _ _ = TmUnit

module Zord.Semantics.StepTrace where

import Prelude

import Control.Monad.Writer (Writer, runWriter, tell)
import Data.Bifunctor (rmap)
import Data.Monoid.Endo (Endo(..))
import Data.Newtype (unwrap)
import Data.Tuple (Tuple)
import Partial.Unsafe (unsafeCrashWith)
import Zord.Semantics.Common (Arg(..), binop, selectLabel, toString, unop)
import Zord.Semantics.Subst (isValue, paraApp, typedReduce)
import Zord.Syntax.Core (Tm(..), tmSubst)
import Zord.Util (unsafeFromJust)

type ShowS = String -> String
type EndoS = Endo Function String
type Eval a = Writer EndoS a

endoS :: String -> EndoS
endoS s = Endo (s <> _)

computation :: String -> Eval Unit
computation w = tell $ endoS $ "↓ Step-" <> w <> "\n"

congruence :: String -> Eval Unit
congruence w = tell $ endoS $ "→ Step-" <> w <> "\n"

eval :: Tm -> Tuple Tm ShowS
eval = go >>> runWriter >>> rmap unwrap
  where go :: Tm -> Eval Tm
        go e | isValue e = tell (endoS $ show e <> "\n") $> e
             | otherwise = tell (endoS $ show e <> "\n") *> step e >>= go

step :: Tm -> Eval Tm
step (TmUnary op e)
  | isValue e = computation "UnaryV" $> unop op e
  | otherwise = congruence  "Unary"  $> TmUnary op <*> step e
step (TmBinary op e1 e2)
  | isValue e1 && isValue e2 = computation "BinaryV" $> binop op e1 e2
  | isValue e1 = congruence "BinaryR" $> TmBinary op e1 <*> step e2
  | otherwise  = congruence "BinaryL" $> TmBinary op <*> step e1 <@> e2
step (TmIf (TmBool true)  e _) = computation "IfTrue"  $> e
step (TmIf (TmBool false) _ e) = computation "IfFalse" $> e
step (TmIf e1 e2 e3) = congruence "If" $> TmIf <*> step e1 <@> e2 <@> e3
step (TmApp e1 e2 coercive)
  | isValue e1 = computation "PApp" $>
                  paraApp e1 ((if coercive then TmAnnoArg else TmArg) e2)
  | otherwise  = congruence  "AppL" $> TmApp <*> step e1 <@> e2 <@> coercive
step fix@(TmFix x e _) = computation "Fix" $> tmSubst x fix e
step (TmAnno (TmAnno e _) t) = computation "AnnoAnno" $> TmAnno e t
step (TmAnno e t)
  | isValue e = computation "AnnoV" $> unsafeFromJust (typedReduce e t)
  | otherwise = congruence  "Anno"  $> TmAnno <*> step e <@> t
step (TmMerge e1 e2)
  | isValue e1 = congruence "MergeR" $> TmMerge e1 <*> step e2
  | isValue e2 = congruence "MergeL" $> TmMerge <*> step e1 <@> e2
  | otherwise  = congruence "Merge"  $> TmMerge <*> step e1 <*> step e2
step (TmPrj e l)
  | isValue e = computation "PProj" $> selectLabel e l
  | otherwise = congruence  "Proj"  $> TmPrj <*> step e <@> l
step (TmTApp e t)
  | isValue e = computation "PTApp" $> paraApp e (TyArg t)
  | otherwise = congruence  "TApp"  $> TmTApp <*> step e <@> t
step (TmToString e)
  | isValue e = computation "ToStringV" $> toString e
  | otherwise = congruence  "ToString"  $> TmToString <*> step e
step e = unsafeCrashWith $ "Zord.Semantics.StepTrace.step: " <>
  "well-typed programs don't get stuck, but got " <> show e

module Zord.Typing where

import Prelude

import Data.List (List(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Zord.Context (Pos(..), Typing, addTmBind, addTyBind, lookupTmBind, lookupTyBind, setPos, throwTypeError)
import Zord.Desugar (transform)
import Zord.Kinding (tySubst, (===))
import Zord.Subtyping (isTopLike, (<:))
import Zord.Syntax.Common (BinOp(..), UnOp(..), (<+>))
import Zord.Syntax.Core as C
import Zord.Syntax.Source as S

synthesize :: S.Tm -> Typing (Tuple C.Tm C.Ty)
synthesize (S.TmInt i)    = pure $ Tuple (C.TmInt i) C.TyInt
synthesize (S.TmDouble d) = pure $ Tuple (C.TmDouble d) C.TyDouble
synthesize (S.TmString s) = pure $ Tuple (C.TmString s) C.TyString
synthesize (S.TmBool b)   = pure $ Tuple (C.TmBool b) C.TyBool
synthesize S.TmUnit = pure $ Tuple C.TmUnit C.TyTop
synthesize (S.TmUnary Neg e) = do
  Tuple e' t <- synthesize e
  let core = C.TmUnary Neg e'
  case t of C.TyInt    -> pure $ Tuple core C.TyInt
            C.TyDouble -> pure $ Tuple core C.TyDouble
            _ -> throwTypeError $ "Neg is not defined for" <+> show t
synthesize (S.TmUnary Not e) = do
  Tuple e' t <- synthesize e
  let core = pure $ Tuple (C.TmUnary Not e') C.TyBool
  case t of C.TyBool -> core
            _ -> throwTypeError $ "Not is not defined for" <+> show t
synthesize (S.TmBinary (Arith op) e1 e2) = do
  Tuple e1' t1 <- synthesize e1
  Tuple e2' t2 <- synthesize e2
  let core = C.TmBinary (Arith op) e1' e2'
  case t1, t2 of C.TyInt,    C.TyInt    -> pure $ Tuple core C.TyInt
                 C.TyDouble, C.TyDouble -> pure $ Tuple core C.TyDouble
                 _, _ -> throwTypeError $ "ArithOp is not defined between" <+>
                                          show t1 <+> "and" <+> show t2
synthesize (S.TmBinary (Comp op) e1 e2) = do
  Tuple e1' t1 <- synthesize e1
  Tuple e2' t2 <- synthesize e2
  let core = pure $ Tuple (C.TmBinary (Comp op) e1' e2') C.TyBool
  case t1, t2 of C.TyInt,    C.TyInt    -> core
                 C.TyDouble, C.TyDouble -> core
                 C.TyString, C.TyString -> core
                 C.TyBool,   C.TyBool   -> core
                 _, _ -> throwTypeError $ "CompOp is not defined between" <+>
                                          show t1 <+> "and" <+> show t2
synthesize (S.TmBinary (Logic op) e1 e2) = do
  Tuple e1' t1 <- synthesize e1
  Tuple e2' t2 <- synthesize e2
  let core = pure $ Tuple (C.TmBinary (Logic op) e1' e2') C.TyBool
  case t1, t2 of C.TyBool, C.TyBool -> core
                 _, _ -> throwTypeError $ "LogicOp is not defined between" <+>
                                          show t1 <+> "and" <+> show t2
synthesize (S.TmIf e1 e2 e3) = do
  Tuple e1' t1 <- synthesize e1
  if t1 === C.TyBool then do
    Tuple e2' t2 <- synthesize e2
    Tuple e3' t3 <- synthesize e3
    if t2 === t3 then pure $ Tuple (C.TmIf e1' e2' e3') t2
    else throwTypeError $ "if-branches expected the same type, but got" <+>
                          show t2 <+> "and" <+> show t3
  else throwTypeError $ "if-condition expected Bool, but got" <+> show t1
synthesize (S.TmVar x) = Tuple (C.TmVar x) <$> lookupTmBind x
synthesize (S.TmApp e1 e2) = do
  Tuple e1' t1 <- synthesize e1
  Tuple e2' t2 <- synthesize e2
  Tuple (C.TmApp e1' e2') <$> appSS t1 t2
synthesize (S.TmAbs (Cons (Tuple x (Just targ)) Nil) e) = do
  let targ' = transform targ
  Tuple e' tret <- addTmBind x targ' $ synthesize e
  pure $ Tuple (C.TmAbs x e' targ' tret) (C.TyArr targ' tret)
synthesize (S.TmAbs (Cons (Tuple x Nothing) Nil) e) = throwTypeError
  "lambda parameters should be annotated (type inference is not implemented)"
synthesize (S.TmAnno e ta) = do
  Tuple e' t <- synthesize e
  let ta' = transform ta
  if t <: ta' then pure $ Tuple (C.TmAnno e' ta') ta' else throwTypeError $
    "annotated" <+> show ta' <+> "is not a supertype of synthesized" <+> show t
synthesize (S.TmMerge e1 e2) = do
  Tuple e1' t1 <- synthesize e1
  Tuple e2' t2 <- synthesize e2
  disjoint t1 t2
  pure $ Tuple (C.TmMerge e1' e2') (C.TyAnd t1 t2)
synthesize (S.TmRec (Cons (Tuple l e) Nil)) = do
  Tuple e' t <- synthesize e
  pure $ Tuple (C.TmRec l e') (C.TyRec l t)
synthesize (S.TmPrj e l) = do
  Tuple e' t <- synthesize e
  mt <- select t
  case mt of
    Just t' -> Tuple (C.TmPrj (C.TmAnno e' t') l) <$>
               appSS' t' (C.TyRec l C.TyTop)
    _ -> throwTypeError $ show t <+> "has no label named" <+> show l
  where
    select :: C.Ty -> Typing (Maybe C.Ty)
    select (C.TyAnd t1 t2) = do
      m1 <- select t1
      m2 <- select t2
      case m1, m2 of Just t1', Just t2' -> pure $ Just (C.TyAnd t1' t2')
                     Just t1', Nothing  -> pure $ Just t1'
                     Nothing,  Just t2' -> pure $ Just t2'
                     Nothing,  Nothing  -> pure Nothing
    select r@(C.TyRec l' t) | l' == l   = pure $ Just r
                            | otherwise = pure Nothing
    select t = throwTypeError $ "projection expected Rec, but got" <+> show t
synthesize (S.TmTApp e ta) = do
  Tuple e' tf <- synthesize e
  let ta' = transform ta
  Tuple (C.TmTApp e' ta') <$> appSS' tf ta'
synthesize (S.TmTAbs (Cons (Tuple a (Just td)) Nil) e) = do
  let td' = transform td
  Tuple e' t <- addTyBind a td' $ synthesize e
  pure $ Tuple (C.TmTAbs a td' e' t) (C.TyForall a td' t)
synthesize (S.TmLet x e1 e2) = do
  Tuple e1' t1 <- synthesize e1
  Tuple e2' t2 <- addTmBind x t1 $ synthesize e2
  pure $ Tuple (C.TmApp (C.TmAbs x e2' t1 t2) e1') t2
synthesize (S.TmPos p e) = setPos (Pos p e) $ synthesize e
synthesize e = throwTypeError $ show e <+> "should have been desugared"

appSS :: C.Ty -> C.Ty -> Typing C.Ty
appSS C.TyTop _ = pure C.TyTop
appSS f@(C.TyArr targ tret) t | t <: targ = pure tret
                              | otherwise = throwTypeError $
  show f <+> "expected a subtype of its parameter type, but got" <+> show t
appSS (C.TyAnd t1 t2) t = do
  t1' <- appSS t1 t
  t2' <- appSS t2 t
  pure $ C.TyAnd t1' t2'
appSS t _ = throwTypeError $ show t <+> "is not applicable"

appSS' :: C.Ty -> C.Ty -> Typing C.Ty
appSS' C.TyTop _ = pure C.TyTop
appSS' (C.TyRec _ t) (C.TyRec _ _) = pure t
appSS' (C.TyForall a td t) ta = disjoint ta td $> tySubst a ta t
appSS' (C.TyAnd t1 t2) t = do
  t1' <- appSS' t1 t
  t2' <- appSS' t2 t
  pure $ C.TyAnd t1' t2'
appSS' t _ = throwTypeError $ show t <+> "is not type-applicable"

disjoint :: C.Ty -> C.Ty -> Typing Unit
disjoint t _ | isTopLike t = pure unit
disjoint _ t | isTopLike t = pure unit
disjoint (C.TyArr _ t1) (C.TyArr _ t2) = disjoint t1 t2
disjoint (C.TyAnd t1 t2) t3 = disjoint t1 t3 *> disjoint t2 t3
disjoint t1 (C.TyAnd t2 t3) = disjoint (C.TyAnd t2 t3) t1
disjoint (C.TyRec l1 t1) (C.TyRec l2 t2) | l1 == l2  = disjoint t1 t2
                                         | otherwise = pure unit
disjoint (C.TyVar a) t = do
  t' <- lookupTyBind a
  if t' <: t then pure unit else throwTypeError $
    "type variable" <+> show a <+> "is not disjoint from" <+> show t
    -- TODO: TyVar name is confusing after substitution in TyForall
disjoint t (C.TyVar a) = disjoint (C.TyVar a) t
disjoint (C.TyForall a1 td1 t1) (C.TyForall a2 td2 t2) =
  addTyBind a1 (C.TyAnd td1 td2) $ disjoint t1 (tySubst a2 (C.TyVar a1) t2)
disjoint t1 t2 | t1 /= t2  = pure unit
               | otherwise = throwTypeError $
  show t1 <+> "and" <+> show t2 <+> "are not disjoint"

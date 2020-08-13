module Zord.Typing where

import Prelude

import Data.List (List(..), foldr)
import Data.Maybe (Maybe(..))
import Data.Set (Set, empty, singleton, union)
import Data.Tuple (Tuple(..), uncurry)
import Zord.Context (Pos(..), Typing, addSort, addTmBind, addTyAlias, addTyBind, lookupTmBind, lookupTyBind, setPos, throwTypeError)
import Zord.Subtyping (isTopLike, (<:), (===))
import Zord.Syntax.Common (BinOp(..), Label, Name, UnOp(..), fromJust, (<+>))
import Zord.Syntax.Core as C
import Zord.Syntax.Source as S
import Zord.Transform (distinguish, transform)

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
  targ' <- transform targ
  Tuple e' tret <- addTmBind x targ' $ synthesize e
  pure $ Tuple (C.TmAbs x e' targ' tret) (C.TyArr targ' tret false)
synthesize (S.TmAbs (Cons (Tuple x Nothing) Nil) e) = throwTypeError
  "lambda parameters should be annotated (type inference is not implemented)"
synthesize (S.TmAnno e ta) = do
  Tuple e' t <- synthesize e
  ta' <- transform ta
  if t <: ta' then pure $ Tuple (C.TmAnno e' ta') ta' else throwTypeError $
    "annotated" <+> show ta' <+> "is not a supertype of synthesized" <+> show t
synthesize (S.TmMerge e1 e2) = do
  Tuple e1' t1 <- synthesize e1
  Tuple e2' t2 <- synthesize e2
  disjoint t1 t2
  pure $ Tuple (C.TmMerge e1' e2') (C.TyAnd t1 t2)
synthesize (S.TmRcd (Cons (Tuple l e) Nil)) = do
  Tuple e' t <- synthesize e
  pure $ Tuple (C.TmRcd l e') (C.TyRcd l t)
synthesize (S.TmPrj e l) = do
  Tuple e' t <- synthesize e
  case selectLabel t l of
    Just t' -> pure $ Tuple (C.TmPrj e' l) t'
    _ -> throwTypeError $ show t <+> "has no label named" <+> show l
synthesize (S.TmTApp e ta) = do
  Tuple e' tf <- synthesize e
  ta' <- transform ta
  Tuple (C.TmTApp e' ta') <$> appSS' tf ta'
synthesize (S.TmTAbs (Cons (Tuple a (Just td)) Nil) e) = do
  td' <- transform td
  Tuple e' t <- addTyBind a td' $ synthesize e
  pure $ Tuple (C.TmTAbs a td' e' t) (C.TyForall a td' t)
synthesize (S.TmLet x e1 e2) = do
  Tuple e1' t1 <- synthesize e1
  Tuple e2' t2 <- addTmBind x t1 $ synthesize e2
  pure $ Tuple (letIn x e1' t1 e2' t2) t2
synthesize (S.TmLetrec x t e1 e2) = do
  t' <- transform t
  Tuple e1' t1 <- addTmBind x t' $ synthesize e1
  if t1 <: t' then do
    Tuple e2' t2 <- addTmBind x t' $ synthesize e2
    pure $ Tuple (letIn x (C.TmFix x e1' t') t' e2' t2) t2
  else throwTypeError $
    "annotated" <+> show t' <+> "is not a supertype of synthesized" <+> show t1
-- TODO: find a more efficient algorithm
synthesize (S.TmOpen e1 e2) = do
  Tuple e1' t1 <- synthesize e1
  let ls = foldr Cons Nil (labels t1)
  let bs = ls <#> \l -> Tuple l (fromJust (selectLabel t1 l))
  Tuple e2' t2 <- foldr (uncurry addTmBind) (synthesize e2) bs
  let open (Tuple l t) e = letIn l (C.TmPrj e1' l) t e t2
  pure $ Tuple (foldr open e2' bs) t2
  where
    labels :: C.Ty -> Set Label
    labels (C.TyAnd t1 t2) = union (labels t1) (labels t2)
    labels (C.TyRcd l _) = singleton l
    labels _ = empty
synthesize (S.TmTrait (Just (Tuple x t)) (Just sig) me1 e2) = do
  t' <- transform t
  sig' <- transform sig
  case me1 of
    Just e1 -> do
      -- TODO: self-reference may have a different name in super-trait
      Tuple e1' t1 <- addTmBind x t' $ synthesize e1
      case t1 of
        C.TyArr ti to true -> do
          if t' <: ti then do
            Tuple e2' t2 <- addTmBind x t' $ addTmBind "super" to $ synthesize e2
            disjoint to t2
            let tret = C.TyAnd to t2
            if tret <: sig' then
              let ret = letIn "super" (C.TmApp e1' (C.TmVar x)) to
                        (C.TmMerge (C.TmVar "super") e2') tret in
              pure $ Tuple (C.TmAbs x ret t' tret) (C.TyArr t' tret true)
            else throwTypeError $ show tret <+> "does not implement" <+> show sig'
          else throwTypeError $ "self-type" <+> show t' <+>
            "is not a subtype of inherited self-type" <+> show to
        _ -> throwTypeError $ "inherits expected a trait, but got" <+> show t1
    Nothing -> do
      Tuple e2' t2 <- addTmBind x t' $ synthesize e2
      if t2 <: sig' then pure $ Tuple (C.TmAbs x e2' t' t2) (C.TyArr t' t2 true)
      else throwTypeError $ show t2 <+> "does not implement" <+> show sig'
synthesize (S.TmNew e) = do
  Tuple e' t <- synthesize e
  case t of
    C.TyArr ti to true ->
      if to <: ti then
        pure $ Tuple (C.TmFix "self" (C.TmApp e' (C.TmVar "self")) to) to
      else throwTypeError $ "in a trait type, input" <+> show ti <+>
        "is not a supertype of output" <+> show to
    _ -> throwTypeError $ "new expected a trait, but got" <+> show t
-- TODO: save original terms instead of desugared ones
synthesize (S.TmPos p e) = setPos (Pos p e) $ synthesize e
synthesize (S.TmType a sorts params Nothing t e) = do
  t' <- addSorts $ distinguish false true t
  addSorts $ addTyAlias a (sig t') $ synthesize e
  where
    addSorts :: forall a. Typing a -> Typing a
    addSorts x = foldr addSort x sorts
    sig :: S.Ty -> S.Ty
    sig t' = foldr S.TySig (foldr S.TyAbs t' params) sorts
synthesize e = throwTypeError $ show e <+> "should have been desugared"

appSS :: C.Ty -> C.Ty -> Typing C.Ty
appSS C.TyTop _ = pure C.TyTop
appSS f@(C.TyArr targ tret _) t | t <: targ = pure tret
                              | otherwise = throwTypeError $
  show f <+> "expected a subtype of its parameter type, but got" <+> show t
appSS (C.TyAnd t1 t2) t = do
  t1' <- appSS t1 t
  t2' <- appSS t2 t
  pure $ C.TyAnd t1' t2'
appSS t _ = throwTypeError $ show t <+> "is not applicable"

appSS' :: C.Ty -> C.Ty -> Typing C.Ty
appSS' C.TyTop _ = pure C.TyTop
appSS' (C.TyForall a td t) ta = disjoint ta td $> C.tySubst a ta t
appSS' (C.TyAnd t1 t2) t = do
  t1' <- appSS' t1 t
  t2' <- appSS' t2 t
  pure $ C.TyAnd t1' t2'
appSS' t _ = throwTypeError $ show t <+> "is not type-applicable"

disjoint :: C.Ty -> C.Ty -> Typing Unit
disjoint t _ | isTopLike t = pure unit
disjoint _ t | isTopLike t = pure unit
disjoint (C.TyArr _ t1 _) (C.TyArr _ t2 _) = disjoint t1 t2
disjoint (C.TyAnd t1 t2) t3 = disjoint t1 t3 *> disjoint t2 t3
disjoint t1 (C.TyAnd t2 t3) = disjoint (C.TyAnd t2 t3) t1
disjoint (C.TyRcd l1 t1) (C.TyRcd l2 t2) | l1 == l2  = disjoint t1 t2
                                         | otherwise = pure unit
disjoint (C.TyVar a) t = do
  mt' <- lookupTyBind a
  case mt' of
    Just t' -> if t' <: t then pure unit else throwTypeError $
      "type variable" <+> show a <+> "is not disjoint from" <+> show t
    Nothing -> throwTypeError $ "type variable" <+> show a <+> "is undefined"
disjoint t (C.TyVar a) = disjoint (C.TyVar a) t
disjoint (C.TyForall a1 td1 t1) (C.TyForall a2 td2 t2) =
  addTyBind freshName (C.TyAnd td1 td2) $
  disjoint (C.tySubst a1 freshVar t1) (C.tySubst a2 freshVar t2)
  where freshName = a1 <> " or " <> a2
        freshVar = C.TyVar freshName
disjoint t1 t2 | t1 /= t2  = pure unit
               | otherwise = throwTypeError $
  show t1 <+> "and" <+> show t2 <+> "are not disjoint"


letIn :: Name -> C.Tm -> C.Ty -> C.Tm -> C.Ty -> C.Tm
letIn x e1 t1 e2 t2 = C.TmApp (C.TmAbs x e2 t1 t2) e1

selectLabel :: C.Ty -> Label -> Maybe C.Ty
selectLabel (C.TyAnd t1 t2) l = case selectLabel t1 l, selectLabel t2 l of
  Just t1', Just t2' -> Just (C.TyAnd t1' t2')
  Just t1', Nothing  -> Just t1'
  Nothing,  Just t2' -> Just t2'
  Nothing,  Nothing  -> Nothing
selectLabel (C.TyRcd l' t) l | l == l' = Just t
selectLabel _ _ = Nothing

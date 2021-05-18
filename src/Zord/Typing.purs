module Zord.Typing where

import Prelude

import Data.Array (all, elem, head, notElem, null, unzip)
import Data.Either (Either(..))
import Data.List (List(..), filter, foldr, last, singleton)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Zord.Context (Pos(..), Typing, addSort, addTmBind, addTyAlias, addTyBind, lookupTmBind, lookupTyBind, setPos, throwTypeError)
import Zord.Desugar (desugar, desugarMethodPattern)
import Zord.Subtyping (isTopLike, (<:), (===))
import Zord.Syntax.Common (BinOp(..), Label, Name, UnOp(..))
import Zord.Syntax.Core as C
import Zord.Syntax.Source as S
import Zord.Transform (duringTransformation, transform, transformTyDef)
import Zord.Util (unsafeFromJust, (<+>))

infer :: S.Tm -> Typing (Tuple C.Tm C.Ty)
infer (S.TmInt i)    = pure $ Tuple (C.TmInt i) C.TyInt
infer (S.TmDouble d) = pure $ Tuple (C.TmDouble d) C.TyDouble
infer (S.TmString s) = pure $ Tuple (C.TmString s) C.TyString
infer (S.TmBool b)   = pure $ Tuple (C.TmBool b) C.TyBool
infer S.TmUnit       = pure $ Tuple C.TmUnit C.TyTop
infer S.TmUndefined  = pure $ Tuple C.TmUndefined C.TyBot
-- Int is always prioritized over Double: e.g. -(1.0,2) = -2
infer (S.TmUnary Neg e) = do
  Tuple e' t <- infer e
  let core ty = Tuple (C.TmUnary Neg (C.TmAnno e' ty)) ty
  if t <: C.TyInt then pure $ core C.TyInt
  else if t <: C.TyDouble then pure $ core C.TyDouble
  else throwTypeError $ "Neg is not defined for" <+> show t
infer (S.TmUnary Not e) = do
  Tuple e' t <- infer e
  let core = Tuple (C.TmUnary Not (C.TmAnno e' C.TyBool)) C.TyBool
  if t <: C.TyBool then pure core
  else throwTypeError $ "Not is not defined for" <+> show t
infer (S.TmUnary Len e) = do
  Tuple e' t <- infer e
  let core = Tuple (C.TmUnary Len e') C.TyInt
  case t of C.TyArray _ -> pure core
            _ -> throwTypeError $ "Len is not defined for" <+> show t
infer (S.TmBinary (Arith op) e1 e2) = do
  Tuple e1' t1 <- infer e1
  Tuple e2' t2 <- infer e2
  let core ty = Tuple (C.TmBinary (Arith op) (C.TmAnno e1' ty)
                                             (C.TmAnno e2' ty)) ty
  if t1 <: C.TyInt && t2 <: C.TyInt then pure $ core C.TyInt
  else if t1 <: C.TyDouble && t2 <: C.TyDouble then pure $ core C.TyDouble
  else throwTypeError $
    "ArithOp is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary (Comp op) e1 e2) = do
  Tuple e1' t1 <- infer e1
  Tuple e2' t2 <- infer e2
  let core ty = Tuple (C.TmBinary (Comp op) (C.TmAnno e1' ty)
                                            (C.TmAnno e2' ty)) C.TyBool
  if t1 <: C.TyInt && t2 <: C.TyInt then pure $ core C.TyInt
  else if t1 <: C.TyDouble && t2 <: C.TyDouble then pure $ core C.TyDouble
  else if t1 <: C.TyString && t2 <: C.TyString then pure $ core C.TyString
  else if t1 <: C.TyBool && t2 <: C.TyBool then pure $ core C.TyBool
  else throwTypeError $
    "CompOp is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary (Logic op) e1 e2) = do
  Tuple e1' t1 <- infer e1
  Tuple e2' t2 <- infer e2
  let core = Tuple (C.TmBinary (Logic op) (C.TmAnno e1' C.TyBool)
                                          (C.TmAnno e2' C.TyBool)) C.TyBool
  if t1 <: C.TyBool && t2 <: C.TyBool then pure core
  else throwTypeError $
    "LogicOp is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary Append e1 e2) = do
  Tuple e1' t1 <- infer e1
  Tuple e2' t2 <- infer e2
  if t1 <: C.TyString && t2 <: C.TyString then
    pure $ Tuple (C.TmBinary Append (C.TmAnno e1' C.TyString)
                                    (C.TmAnno e2' C.TyString)) C.TyString
  else case t1, t2 of
    C.TyArray t1', C.TyArray t2' | t1' === t2' ->
      pure $ Tuple (C.TmBinary Append e1' e2') (C.TyArray t1')
    _, _ -> throwTypeError $
      "Append is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary Index e1 e2) = do
  Tuple e1' t1 <- infer e1
  Tuple e2' t2 <- infer e2
  let core = C.TmBinary Index e1' e2'
  case t1, t2 of C.TyArray t1', C.TyInt -> pure $ Tuple core t1'
                 _, _ -> throwTypeError $ "Index is not defined between" <+>
                                          show t1 <+> "and" <+> show t2
infer (S.TmIf e1 e2 e3) = do
  Tuple e1' t1 <- infer e1
  if t1 <: C.TyBool then do
    Tuple e2' t2 <- infer e2
    Tuple e3' t3 <- infer e3
    if t2 === t3 then pure $ Tuple (C.TmIf (C.TmAnno e1' C.TyBool) e2' e3') t2
    else throwTypeError $ "if-branches expected the same type, but got" <+>
                          show t2 <+> "and" <+> show t3
  else throwTypeError $ "if-condition expected Bool, but got" <+> show t1
infer (S.TmVar x) = Tuple (C.TmVar x) <$> lookupTmBind x
infer (S.TmApp e1 e2) = do
  Tuple e1' t1 <- infer e1
  Tuple e2' t2 <- infer e2
  Tuple (C.TmApp e1' e2' true) <$> distApp t1 (Left t2)
infer (S.TmAbs (Cons (S.TmParam x (Just targ)) Nil) e) = do
  targ' <- transform targ
  Tuple e' tret <- addTmBind x targ' $ infer e
  pure $ Tuple (C.TmAbs x e' targ' tret) (C.TyArrow targ' tret false)
infer (S.TmAbs (Cons (S.TmParam x Nothing) Nil) _) = throwTypeError $
  "lambda parameter" <+> show x <+> "should be annotated with a type"
infer (S.TmAnno e ta) = do
  Tuple e' t <- infer e
  ta' <- transform ta
  if t <: ta' then pure $ Tuple (C.TmAnno e' ta') ta' else throwTypeError $
    "annotated" <+> show ta <+> "is not a supertype of inferred" <+> show t
infer (S.TmMerge e1 e2) = do
  Tuple e1' t1 <- infer e1
  Tuple e2' t2 <- infer e2
  case t1, t2 of
    C.TyArrow targ1 tret1 true, C.TyArrow targ2 tret2 true -> do
      disjoint tret1 tret2
      pure $ trait "self" (C.TmMerge (appToSelf e1') (appToSelf e2'))
                   (C.TyAnd targ1 targ2) (C.TyAnd tret1 tret2)
    _, _ -> do
      disjoint t1 t2
      pure $ Tuple (C.TmMerge e1' e2') (C.TyAnd t1 t2)
  where appToSelf e = C.TmApp e (C.TmVar "self") true
infer (S.TmRcd (Cons (S.RcdField _ l Nil (Left e)) Nil)) = do
  Tuple e' t <- infer e
  pure $ Tuple (C.TmRcd l t e') (C.TyRcd l t)
infer (S.TmPrj e l) = do
  Tuple e' t <- infer e
  case selectLabel t l of
    Just t' -> pure $ Tuple (C.TmPrj e' l) t'
    _ -> throwTypeError $ show t <+> "has no label named" <+> show l
infer (S.TmTApp e ta) = do
  Tuple e' tf <- infer e
  ta' <- transform ta
  Tuple (C.TmTApp e' ta') <$> distApp tf (Right ta')
infer (S.TmTAbs (Cons (Tuple a (Just td)) Nil) e) = do
  td' <- transform td
  Tuple e' t <- addTyBind a td' $ infer e
  pure $ Tuple (C.TmTAbs a td' e' t) (C.TyForall a td' t)
infer (S.TmLet x e1 e2) = do
  Tuple e1' t1 <- infer e1
  Tuple e2' t2 <- addTmBind x t1 $ infer e2
  pure $ Tuple (letIn x e1' t1 e2' t2) t2
infer (S.TmLetrec x t e1 e2) = do
  t' <- transform t
  Tuple e1' t1 <- addTmBind x t' $ infer e1
  -- The return type is constrained to be equivalent to the annotated type
  -- in order to avoid extra typed reduction.
  if t1 === t' then do
    Tuple e2' t2 <- addTmBind x t' $ infer e2
    pure $ Tuple (letIn x (C.TmFix x e1' t') t' e2' t2) t2
  else throwTypeError $
    "annotated" <+> show t' <+> "is different from inferred" <+> show t1
-- TODO: find a more efficient algorithm
infer (S.TmOpen e1 e2) = do
  Tuple e1' t1 <- infer e1
  let ls = foldr Cons Nil (labels t1)
  let bs = ls <#> \l -> Tuple l (unsafeFromJust (selectLabel t1 l))
  Tuple e2' t2 <- foldr (uncurry addTmBind) (infer e2) bs
  let open (Tuple l t) e = letIn l (C.TmPrj e1' l) t e t2
  pure $ Tuple (foldr open e2' bs) t2
  where
    labels :: C.Ty -> Set Label
    labels (C.TyAnd t1 t2) = Set.union (labels t1) (labels t2)
    labels (C.TyRcd l _) = Set.singleton l
    labels _ = Set.empty
infer (S.TmTrait (Just (Tuple self t)) (Just sig) me1 ne2) = do
  t' <- transform t
  Tuple sig' e2 <- inferFromSig `duringTransformation` Tuple sig ne2
  Tuple ret tret <- case me1 of
    Just e1 -> do
      -- TODO: self-reference may have a different name in super-trait
      Tuple e1' t1 <- addTmBind self t' $ infer e1
      case t1 of
        C.TyArrow ti to true -> do
          if t' <: ti then do
            Tuple e2' t2 <-
              addTmBind self t' $ addTmBind "super" to $ infer e2
            let to' = override to e2
            disjoint to' t2
            let tret = C.TyAnd to' t2
            let ret = letIn "super" (C.TmApp e1' (C.TmVar self) true) to
                      (C.TmMerge (C.TmAnno (C.TmVar "super") to') e2') tret
            pure $ Tuple ret tret
          else throwTypeError $ "self-type" <+> show t <+>
            "is not a subtype of inherited self-type" <+> show to
        _ -> throwTypeError $ "expected to inherit a trait, but got" <+> show t1
    Nothing -> do
      Tuple e2' t2 <- addTmBind self t' $ infer e2
      pure $ Tuple e2' t2
  if tret <: sig' then pure $ trait self ret t' tret
  else throwTypeError $ show sig <+> "is not implemented by the trait," <+>
                        "whose type is" <+> show tret
  where
    -- TODO: inference is not complete
    inferFromSig :: S.Ty -> S.Tm -> S.Tm
    inferFromSig rs@(S.TyAnd _ _) e = inferFromSig (S.TyRcd $ combineRcd rs) e
    inferFromSig s (S.TmPos p e) = S.TmPos p (inferFromSig s e)
    inferFromSig s (S.TmOpen e1 e2) = S.TmOpen e1 (inferFromSig s e2)
    inferFromSig s (S.TmMerge e1 e2) =
      S.TmMerge (inferFromSig s e1) (inferFromSig s e2)
    inferFromSig (S.TyRcd xs) r@(S.TmRcd (Cons (S.RcdField o l Nil (Left e)) Nil)) =
      case last $ filter (\x -> fst x == l) xs of
        Just (Tuple _ ty) ->
          S.TmRcd (singleton (S.RcdField o l Nil (Left (inferFromSig ty e))))
        _ -> r
    inferFromSig (S.TyRcd xs) (S.TmRcd (Cons (S.DefaultPattern pat) Nil)) =
      let S.MethodPattern _ l _ _ = pat in
      desugar $ S.TmRcd $ filter (\x -> fst x `notElem` patterns l) xs <#> \x ->
        let Tuple params ty = paramsAndInnerTy (snd x) in
        let e = inferFromSig ty (desugarMethodPattern pat) in
        S.RcdField false (fst x) params (Left e)
    inferFromSig (S.TyArrow targ tret) (S.TmAbs (Cons (S.TmParam x Nothing) Nil) e) =
      S.TmAbs (singleton (S.TmParam x (Just targ))) (inferFromSig tret e)
    inferFromSig (S.TyArrow _ tret)
                 (S.TmAbs param@(Cons (S.TmParam _ (Just _)) Nil) e) =
      S.TmAbs param (inferFromSig tret e)
    inferFromSig (S.TyTrait ti to) (S.TmTrait (Just (Tuple self' t')) sig' e1 e2) =
      let t'' = if t' == S.TyTop then fromMaybe S.TyTop ti else t' in
      S.TmTrait (Just (Tuple self' t'')) sig' e1 (inferFromSig to e2)
    inferFromSig _ e = e
    combineRcd :: S.Ty -> S.RcdTyList
    combineRcd (S.TyAnd (S.TyRcd xs) (S.TyRcd ys)) = xs <> ys
    combineRcd (S.TyAnd l (S.TyRcd ys)) = combineRcd l <> ys
    combineRcd (S.TyAnd (S.TyRcd xs) r) = xs <> combineRcd r
    combineRcd (S.TyAnd l r) = combineRcd l <> combineRcd r
    combineRcd _ = Nil
    patterns :: Label -> Array Label
    patterns l = patternsFromRcd (S.TmMerge (fromMaybe S.TmUnit me1) ne2) l
    patternsFromRcd :: S.Tm -> Label -> Array Label
    patternsFromRcd (S.TmPos _ e) l = patternsFromRcd e l
    patternsFromRcd (S.TmOpen _ e) l = patternsFromRcd e l
    patternsFromRcd (S.TmMerge e1 e2) l = patternsFromRcd e1 l <> patternsFromRcd e2 l
    patternsFromRcd (S.TmRcd (Cons (S.RcdField _ l' _ (Left e)) Nil)) l =
      if innerLabel e == l then [l'] else []
    patternsFromRcd _ _ = []
    innerLabel :: S.Tm -> Label
    innerLabel (S.TmPos _ e) = innerLabel e
    innerLabel (S.TmOpen _ e) = innerLabel e
    innerLabel (S.TmAbs _ e) = innerLabel e
    innerLabel (S.TmTrait _ _ _ e) = innerLabel e
    innerLabel (S.TmRcd (Cons (S.RcdField _ l _ _) Nil)) = l
    innerLabel _ = "#nothing"
    paramsAndInnerTy :: S.Ty -> Tuple S.TmParamList S.Ty
    paramsAndInnerTy (S.TyArrow targ tret) =
      let Tuple params ty = paramsAndInnerTy tret in
      Tuple (Cons (S.TmParam "_" (Just targ)) params) ty
    paramsAndInnerTy ty = Tuple Nil ty
    selectOverride :: S.Tm -> Array Label
    selectOverride (S.TmPos _ e) = selectOverride e
    selectOverride (S.TmOpen _ e) = selectOverride e
    selectOverride (S.TmMerge e1 e2) = selectOverride e1 <> selectOverride e2
    -- TODO: only override the inner field if it's a method pattern
    selectOverride (S.TmRcd (Cons (S.RcdField true l _ _) Nil)) = [l]
    selectOverride _ = []
    -- TODO: make sure every field overrides some field in super-trait
    removeOverride :: C.Ty -> Array Label -> C.Ty
    removeOverride (C.TyAnd t1 t2) ls =
      let t1' = removeOverride t1 ls in
      let t2' = removeOverride t2 ls in
      case t1', t2' of
        C.TyTop, C.TyTop -> C.TyTop
        C.TyTop, _       -> t2'
        _,       C.TyTop -> t1'
        _,       _       -> C.TyAnd t1' t2'
    removeOverride (C.TyRcd l _) ls | l `elem` ls = C.TyTop
    removeOverride ty _ = ty
    override :: C.Ty -> S.Tm -> C.Ty
    override ty e = let ls = selectOverride e in
      if null ls then ty else removeOverride ty ls
infer (S.TmTrait self sig e1 e2) =
  infer $ S.TmTrait (Just (fromMaybe (Tuple "self" S.TyTop) self))
                    (Just (fromMaybe S.TyTop sig)) e1 e2
infer (S.TmNew e) = do
  Tuple e' t <- infer e
  case t of
    C.TyArrow ti to true ->
      if to <: ti then
        pure $ Tuple (C.TmFix "self" (C.TmApp e' (C.TmVar "self") true) to) to
      else throwTypeError $ "Trait input" <+> show ti <+>
        "is not a supertype of Trait output" <+> show to
    _ -> throwTypeError $ "new expected a trait, but got" <+> show t
infer (S.TmForward e1 e2) = do
  Tuple e1' t1 <- infer e1
  Tuple e2' t2 <- infer e2
  case t1 of
    C.TyArrow ti to true ->
      if t2 <: ti then pure $ Tuple (C.TmApp e1' e2' true) to
      else throwTypeError $ "expected to forward to a subtype of" <+> show ti <>
                            ", but got" <+> show t2
    _ -> throwTypeError $ "expected to forward from a trait, but got" <+> show t1
infer (S.TmExclude e te) = do
  Tuple e' t <- infer e
  te' <- transform te
  case t of
    C.TyArrow ti to true -> case te' of
      -- TODO: support intersection of multiple record types
      C.TyRcd l tl ->
        let Tuple overridden to' = exclude to l tl in
        let t' = C.TyArrow ti to' true in
        if overridden then pure $ Tuple (C.TmAnno e' t') t'
        else throwTypeError $ show e <+> "does not contain a field of" <+> show te
      _ -> throwTypeError $ "expected to exclude a single-field record type," <+>
                            "but got" <+> show te
    _ -> throwTypeError $ "expected to exclude from a trait, but got" <+> show e
  where
    exclude :: C.Ty -> Label -> C.Ty -> Tuple Boolean C.Ty
    exclude (C.TyAnd t1 t2) l t =
      let Tuple o1 t1' = exclude t1 l t in
      let Tuple o2 t2' = exclude t2 l t in
      Tuple (o1 || o2) (C.TyAnd t1' t2')
    exclude (C.TyRcd l' t') l t | l == l' && t' === t = Tuple true C.TyTop
    exclude t _ _ = Tuple false t
infer (S.TmToString e) = do
  Tuple e' t <- infer e
  if t == C.TyInt || t == C.TyDouble || t == C.TyString || t == C.TyBool
  then pure $ Tuple (C.TmToString e') C.TyString
  else throwTypeError $ "cannot show" <+> show t
infer (S.TmArray arr) = do
  if null arr then
    pure $ Tuple (C.TmArray C.TyBot []) (C.TyArray C.TyBot)
  else do
    ets <- traverse infer arr
    let Tuple es ts = unzip ets
    let t = unsafeFromJust $ head ts
    if all (_ === t) ts then pure $ Tuple (C.TmArray t es) (C.TyArray t)
    else throwTypeError $ "elements of" <+> show (S.TmArray arr) <+>
                          "should all have the same type"
-- TODO: save original terms instead of desugared ones
infer (S.TmPos p e) = setPos (Pos p e) $ infer e
infer (S.TmType a sorts params Nothing t e) = do
  t' <- addSorts $ addTyBinds $ transformTyDef t
  addTyAlias a (sig t') $ infer e
  where
    dualSorts :: List (Tuple Name Name)
    dualSorts = sorts <#> \sort -> Tuple sort ("#" <> sort)
    addSorts :: forall a. Typing a -> Typing a
    addSorts typing = foldr (uncurry addSort) typing dualSorts
    addTyBinds :: forall a. Typing a -> Typing a
    addTyBinds typing = foldr (flip addTyBind C.TyTop) typing params
    sig :: S.Ty -> S.Ty
    sig t' = foldr (uncurry S.TySig) (foldr S.TyAbs t' params) dualSorts
infer e = throwTypeError $ show e <+> "should have been desugared"

distApp :: C.Ty -> Either C.Ty C.Ty -> Typing C.Ty
distApp C.TyTop _ = pure C.TyTop
distApp f@(C.TyArrow targ tret _) (Left t) | t <: targ = pure tret
                                           | otherwise = throwTypeError $
  show f <+> "expected a subtype of its parameter type, but got" <+> show t
distApp (C.TyForall a td t) (Right ta) = disjoint ta td $> C.tySubst a ta t
distApp (C.TyAnd t1 t2) t = do
  t1' <- distApp t1 t
  t2' <- distApp t2 t
  pure $ C.TyAnd t1' t2'
distApp t _ = throwTypeError $ show t <+> "is not applicable"

disjoint :: C.Ty -> C.Ty -> Typing Unit
disjoint t _ | isTopLike t = pure unit
disjoint _ t | isTopLike t = pure unit
disjoint (C.TyArrow _ t1 _) (C.TyArrow _ t2 _) = disjoint t1 t2
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
letIn x e1 t1 e2 t2 = C.TmApp (C.TmAbs x e2 t1 t2) e1 false

trait :: Name -> C.Tm -> C.Ty -> C.Ty -> Tuple C.Tm C.Ty
trait x e targ tret = Tuple (C.TmAbs x e targ tret) (C.TyArrow targ tret true)

selectLabel :: C.Ty -> Label -> Maybe C.Ty
selectLabel (C.TyAnd t1 t2) l = case selectLabel t1 l, selectLabel t2 l of
  Just t1', Just t2' -> Just (C.TyAnd t1' t2')
  Just t1', Nothing  -> Just t1'
  Nothing,  Just t2' -> Just t2'
  Nothing,  Nothing  -> Nothing
selectLabel (C.TyRcd l' t) l | l == l' = Just t
selectLabel _ _ = Nothing

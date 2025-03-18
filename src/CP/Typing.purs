module Language.CP.Typing where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.Error.Class (throwError)
import Control.Monad.State (gets, modify_)
import Data.Array (head, null, unzip)
import Data.Bifunctor (rmap)
import Data.Either (Either(..), either)
import Data.Foldable (all, elem, foldM, foldl, foldr, lookup, notElem, traverse_)
import Data.List (List(..), filter, last, singleton, (:))
import Data.Maybe (Maybe(..), fromMaybe, isJust, maybe)
import Data.Set as Set
import Data.Traversable (for, traverse)
import Data.Tuple (fst, snd, uncurry)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Context (Checking, Pos(..), TypeError(..), Typing, addSort, addTmBind, addTyBind, fromState, localPos, lookupTmBind, lookupTyBind, runTyping, throwTypeError)
import Language.CP.Subtyping (isTopLike, (<:), (===))
import Language.CP.Syntax.Common (BinOp(..), CompOp(..), Label, Name, UnOp(..))
import Language.CP.Syntax.Core as C
import Language.CP.Syntax.Source as S
import Language.CP.Transform (transform, transform', transformTyDef)
import Language.CP.TypeDiff (tyDiff)
import Language.CP.Util (foldl1, foldr1, unsafeFromJust, (<+>))

infer :: S.Tm -> Typing (C.Tm /\ C.Ty)
infer (S.TmInt i)    = pure $ C.TmInt i /\ C.TyInt
infer (S.TmDouble d) = pure $ C.TmDouble d /\ C.TyDouble
infer (S.TmString s) = pure $ C.TmString s /\ C.TyString
infer (S.TmBool b)   = pure $ C.TmBool b /\ C.TyBool
infer S.TmUnit       = pure $ C.TmUnit /\ C.TyUnit
infer S.TmUndefined  = pure $ C.TmUndefined /\ C.TyBot
-- Int is always prioritized over Double: e.g. -(1.0,2) = -2
infer (S.TmUnary Neg e) = do
  e' /\ t <- infer e
  let core ty = C.TmUnary Neg (C.TmAnno e' ty) /\ ty
  if t <: C.TyInt then pure $ core C.TyInt
  else if t <: C.TyDouble then pure $ core C.TyDouble
  else throwTypeError $ "Neg is not defined for" <+> show t
infer (S.TmUnary Len e) = do
  e' /\ t <- infer e
  let core = C.TmUnary Len e' /\ C.TyInt
  case t of C.TyArray _ -> pure core
            _ -> throwTypeError $ "Len is not defined for" <+> show t
infer (S.TmUnary Sqrt e) = do
  e' /\ t <- infer e
  let core = C.TmUnary Sqrt e' /\ C.TyDouble
  case t of C.TyDouble -> pure core
            _ -> throwTypeError $ "Sqrt is not defined for" <+> show t
infer (S.TmBinary (Arith op) e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  let core ty = C.TmBinary (Arith op) (C.TmAnno e1' ty) (C.TmAnno e2' ty) /\ ty
  if t1 <: C.TyInt && t2 <: C.TyInt then pure $ core C.TyInt
  else if t1 <: C.TyDouble && t2 <: C.TyDouble then pure $ core C.TyDouble
  else throwTypeError $
    "ArithOp is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary (Comp op) e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  let core ty = C.TmBinary (Comp op) (C.TmAnno e1' ty)
                                     (C.TmAnno e2' ty) /\ C.TyBool
  if t1 <: C.TyInt && t2 <: C.TyInt then pure $ core C.TyInt
  else if t1 <: C.TyDouble && t2 <: C.TyDouble then pure $ core C.TyDouble
  else if t1 <: C.TyString && t2 <: C.TyString then pure $ core C.TyString
  else if t1 <: C.TyBool && t2 <: C.TyBool then pure $ core C.TyBool
  else case t1, t2, isEqlOrNeq op of
    C.TyRef _, C.TyRef _, true -> pure $ C.TmBinary (Comp op) e1' e2' /\ C.TyBool
    _, _, _ -> throwTypeError $
      "CompOp is not defined between" <+> show t1 <+> "and" <+> show t2
  where isEqlOrNeq :: CompOp -> Boolean
        isEqlOrNeq Eql = true
        isEqlOrNeq Neq = true
        isEqlOrNeq _ = false
infer (S.TmBinary (Logic op) e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  let core = C.TmBinary (Logic op) (C.TmAnno e1' C.TyBool)
                                   (C.TmAnno e2' C.TyBool) /\ C.TyBool
  if t1 <: C.TyBool && t2 <: C.TyBool then pure core
  else throwTypeError $
    "LogicOp is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary Append e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  if t1 <: C.TyString && t2 <: C.TyString then
    pure $ C.TmBinary Append (C.TmAnno e1' C.TyString)
                             (C.TmAnno e2' C.TyString) /\ C.TyString
  else case t1, t2 of
    C.TyArray t1', C.TyArray t2' ->
      let core el er ty = C.TmBinary Append el er /\ ty in
      if t1' === t2' then pure $ core e1' e2' t1
      else if t2' <: t1' then pure $ core e1' (C.TmAnno e2' t1) t1
      else if t1' <: t2' then pure $ core (C.TmAnno e1' t2) e2' t2
      else throwTypeError $
        "Append expected two arrays of equivalent types or subtypes," <+>
        "but got" <+> show t1' <+> "and" <+> show t2'
    _, _ -> throwTypeError $
      "Append is not defined between" <+> show t1 <+> "and" <+> show t2
infer (S.TmBinary Index e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  case t1 of C.TyArray t1' | t2 <: C.TyInt ->
               pure $ C.TmBinary Index e1' (C.TmAnno e2' C.TyInt) /\ t1'
             _ -> throwTypeError $ "Index is not defined between" <+>
                                   show t1 <+> "and" <+> show t2
infer (S.TmIf e1 e2 e3) = do
  e1' /\ t1 <- infer e1
  if t1 <: C.TyBool then do
    e2' /\ t2 <- infer e2
    e3' /\ t3 <- infer e3
    let core et ef ty = C.TmIf (C.TmAnno e1' C.TyBool) et ef /\ ty
    if t2 === t3 then pure $ core e2' e3' t2
    else if t3 <: t2 then pure $ core e2' (C.TmAnno e3' t2) t2
    else if t2 <: t3 then pure $ core (C.TmAnno e2' t3) e3' t3
    else throwTypeError $
      "if-branches expected two equivalent types or subtypes, but got" <+>
      show t2 <+> "and" <+> show t3
  else throwTypeError $ "if-condition expected Bool, but got" <+> show t1
infer (S.TmVar x) = (C.TmVar x /\ _) <$> lookupTmBind x
infer (S.TmApp e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  case t1 of C.TyArrow targ tret _ | t2 === targ -> pure $ C.TmApp e1' e2' false /\ tret
                                   | labels@(_:_) <- collectOpt targ, t2 `andOpt` labels <: targ ->
                                       let merge acc l = C.TmMerge acc (C.TmRcd l C.TyUnit C.TmUnit)
                                           e2'' = foldl merge e2' labels in
                                       pure $ C.TmApp e1' e2'' false /\ tret
             _ -> (C.TmApp e1' e2' true /\ _) <$> distApp t1 (Left t2)
  where collectOpt :: C.Ty -> List Label  -- TODO: collect optional labels in a safer way
        collectOpt (C.TyAnd t1 t2) = collectOpt t1 <> collectOpt t2
        collectOpt (C.TyRcd l (C.TyOr _ C.TyUnit)) = singleton l
        collectOpt _ = Nil
        andOpt = foldl (\acc l -> C.TyAnd acc (C.TyRcd l C.TyUnit))
infer (S.TmAbs (S.TmParam x (Just targ) : Nil) e) = do
  targ' <- transform targ
  e' /\ tret <- addTmBind x targ' $ infer e
  pure $ C.TmAbs x e' targ' tret false false /\ C.TyArrow targ' tret false
infer (S.TmAbs (S.TmParam x Nothing : Nil) _) = throwTypeError $
  "lambda parameter" <+> show x <+> "should be annotated with a type"
infer (S.TmAbs (S.NamedParams _ true : Nil) _) = throwTypeError $
  "wildcards in named arguments should only occur in traits with interfaces"
infer (S.TmAbs (S.NamedParams fields false : Nil) e) = do
  targ /\ letins /\ tbinds <- foldM collect (C.TyTop /\ Nil /\ Nil) fields
  e' /\ tret <- foldr (uncurry addTmBind) (infer e) tbinds
  pure $ C.TmAbs "$args" (foldl (\body f -> f body tret) e' letins) targ tret false false
      /\ C.TyArrow targ tret false
  where collect (targ /\ letins /\ tbinds) (S.RequiredField l t) = do
          t' <- transform t
          pure $ C.TyAnd targ (C.TyRcd l t')
              /\ (letIn l (C.TmPrj (C.TmVar "$args") l) t' : letins)
              /\ ((l /\ t') : tbinds)
        collect (targ /\ letins /\ tbinds) (S.OptionalField l default) = do
          default' /\ t <- infer default
          let cases = (t /\ C.TmVar l) : (C.TyUnit /\ default') : Nil
              switch = C.TmSwitch (C.TmPrj (C.TmVar "$args") l) l cases
          pure $ C.TyAnd targ (C.TyRcd l (C.TyOr t C.TyUnit))
              /\ (letIn l switch t : letins)
              /\ ((l /\ t) : tbinds)
infer (S.TmAbs xs e) = infer $ foldr (\x s -> S.TmAbs (singleton x) s) e xs
infer (S.TmFix x e t) = do
  t' <- transform t
  e' /\ t'' <- addTmBind x t' $ infer e
  if t'' <: t' then pure $ C.TmFix x e' t'' /\ t'' else throwTypeError $
    "fix body expected a subtype of the annotated type, but got " <+> show t''
infer (S.TmAnno e ta) = do
  e' /\ t <- infer e
  ta' <- transform ta
  if t <: ta' then pure $ C.TmAnno e' ta' /\ ta' else throwTypeError $
    "annotated" <+> show ta <+> "is not a supertype of inferred" <+> show t
infer (S.TmMerge S.Neutral e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  case t1, t2 of
    C.TyTop, _ -> pure $ e2' /\ t2
    _, C.TyTop -> pure $ e1' /\ t1
    C.TyArrow ti1 to1 true, C.TyArrow ti2 to2 true -> do
      disjoint to1 to2
      let ti = case ti1, ti2 of C.TyTop, _ -> ti2
                                _, C.TyTop -> ti1
                                _, _ -> C.TyAnd ti1 ti2
      pure $ trait "$self" (C.TmMerge (appToSelf e1') (appToSelf e2')) ti (C.TyAnd to1 to2)
    _, _ -> do
      disjoint t1 t2
      pure $ C.TmMerge e1' e2' /\ C.TyAnd t1 t2
  where appToSelf e = C.TmApp e (C.TmVar "$self") true
infer (S.TmMerge S.Leftist e1 e2) =
  infer $ S.TmMerge S.Neutral e1 (S.TmDiff e2 e1)
infer (S.TmMerge S.Rightist e1 e2) =
  infer $ S.TmMerge S.Neutral (S.TmDiff e1 e2) e2
-- TODO: make sure case types are disjoint
infer (S.TmSwitch e alias cases) = do
  tte <- for cases \(ti /\ ei) -> do
    ti' <- transform ti
    ei' /\ to <- maybe identity (\x -> addTmBind x ti') alias $ infer ei
    pure $ to /\ ti' /\ ei'
  case maximal (fst <$> tte) of
    Just to -> do
      let cases' = snd <$> tte
          union = foldl1 C.TyOr (fst <$> cases')
      e' /\ t <- infer e
      if t <: union then
        let switch = C.TmSwitch e' (fromMaybe "$alias" alias) cases' in
        pure $ C.TmAnno switch to /\ to
      else throwTypeError $ "switch expression expected a subtype of" <+> show union
                         <> ", but got" <+> show t
    Nothing -> throwTypeError $ "switch cases have different types"
  where maximal :: List C.Ty -> Maybe C.Ty
        maximal Nil = Just C.TyBot
        maximal (t : ts) = do
          t' <- maximal ts
          if t <: t' then Just t'
          else if t' <: t then Just t
          else Nothing
infer (S.TmRcd Nil) = pure $ C.TmTop /\ C.TyTop
infer (S.TmRcd (S.RcdField _ l Nil (Left e) : Nil)) = do
  e' /\ t <- infer e
  pure $ C.TmRcd l t e' /\ C.TyRcd l t
infer (S.TmRcd xs) =
  infer $ foldl1 (S.TmMerge S.Neutral) (xs <#> \x -> S.TmRcd (singleton (desugarField x)))
infer (S.TmPrj e l) = do
  e' /\ t <- infer e
  let r /\ tr = case t of C.TyRec _ _ -> C.TmUnfold t e' /\ C.unfold t
                          _ -> e' /\ t
  case selectLabel tr l of
    Just t' -> pure $ C.TmPrj r l /\ t'
    _ -> throwTypeError $ "label" <+> show l <+> "is absent in" <+> show t
infer (S.TmTApp e ta) = do
  e' /\ tf <- infer e
  ta' <- transform ta
  t <- distApp tf (Right ta')
  pure $ C.TmTApp e' ta' /\ t 
infer (S.TmTAbs ((a /\ Just td) : Nil) e) = do
  td' <- transform td
  e' /\ t <- addTyBind a td' $ infer e
  pure $ C.TmTAbs a td' e' t false /\ C.TyForall a td' t
infer (S.TmTAbs xs e) =
  infer $ foldr (\x s -> S.TmTAbs (singleton (rmap disjointness x)) s) e xs
  where disjointness t = Just (fromMaybe S.TyTop t)
infer (S.TmLet x Nil Nil e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- addTmBind x t1 $ infer e2
  pure $ letIn x e1' t1 e2' t2 /\ t2
infer (S.TmLet x tyParams tmParams e1 e2) =
  infer $ S.TmLet x Nil Nil (S.TmTAbs tyParams (S.TmAbs tmParams e1)) e2
infer (S.TmLetrec x Nil Nil t e1 e2) = do
  e1' /\ t1 <- inferRec x e1 t
  e2' /\ t2 <- addTmBind x t1 $ infer e2
  pure $ letIn x (C.TmFix x e1' t1) t1 e2' t2 /\ t2
infer (S.TmLetrec x tyParams tmParams t e1 e2) =
  infer $ S.TmLetrec x Nil Nil t' (S.TmTAbs tyParams (S.TmAbs tmParams e1)) e2
  where t' = tyOfParams tyParams tmParams t
-- TODO: find a more efficient algorithm
infer (S.TmOpen e1 e2) = do
  e1' /\ t1 <- infer e1
  let r /\ tr = case t1 of C.TyRec _ _ -> C.TmUnfold t1 e1' /\ C.unfold t1
                           _ -> e1' /\ t1
      b = foldr (\l s -> (l /\ unsafeFromJust (selectLabel tr l)) : s)
                Nil (collectLabels tr)
  e2' /\ t2 <- foldr (uncurry addTmBind) (infer e2) b
  -- `open` is the only construct that elaborates to a lazy definition
  let open (l /\ t) e = letIn l (C.TmPrj (C.TmVar "$open") l) t e t2
  pure $ letIn "$open" r tr (foldr open e2' b) t2 /\ t2
infer (S.TmUpdate rcd fields) = do
  rcd' /\ t <- infer rcd
  fields' <- for fields \(l /\ e) -> do
    e' /\ t' <- infer e
    pure $ C.TmRcd l t' e'
  let t' = foldr rcdTy C.TyTop fields'
  if t <: t' then do
    d <- tyDiff t t'
    let merge = if isTopLike d then identity else C.TmMerge (C.TmAnno rcd' d)
        updating = foldr1 C.TmMerge fields'
    pure $ merge updating /\ t
  else throwTypeError $ "cannot safely update the record" <+> show rcd
  where rcdTy :: C.Tm -> C.Ty -> C.Ty
        rcdTy (C.TmRcd l t _) s = C.TyAnd (C.TyRcd l t) s
        rcdTy _ s = s
infer (S.TmTrait (Just (self /\ Just t)) (Just sig) me1 ne2) = do
  t' <- transform t
  sig'' /\ sig' <- transform' sig
  e2 <- inferFromSig sig' ne2
  ret /\ tret <- case me1 of
    Just e1 -> do
      -- self may be used in e1 (e.g. trait [self:T] inherits f self => ...)
      -- this self has nothing to do with that self in the super-trait
      e1' /\ t1 <- addTmBind self t' $ infer e1
      case t1 of
        C.TyArrow ti to true -> do
          if t' <: ti then do
            e2' /\ t2 <-
              addTmBind self t' $ addTmBind "super" to $ infer e2
            let to' = override to e2
            disjoint to' t2
            let tret = C.TyAnd to' t2
                ret = letIn "super" (C.TmApp e1' (C.TmVar self) true) to
                      (C.TmMerge (C.TmAnno (C.TmVar "super") to') e2') tret
            pure $ ret /\ tret
          else throwTypeError $ "self-type" <+> show t <+>
            "is not a subtype of inherited self-type" <+> show ti
        _ -> throwTypeError $ "expected to inherit a trait, but got" <+> show t1
    Nothing -> do
      e2' /\ t2 <- addTmBind self t' $ infer e2
      pure $ e2' /\ t2
  if tret <: sig'' then pure $ trait self ret t' tret
  else throwTypeError $ "the trait does not implement" <+> show sig
  where
    -- TODO: inference is not complete
    inferFromSig :: S.Ty -> S.Tm -> Typing S.Tm
    inferFromSig rs@(S.TyAnd _ _) e = inferFromSig (S.TyRcd $ combineRcd rs) e
    inferFromSig s@(S.TyRec _ ty) e = S.TmFold s <$> inferFromSig ty e
    inferFromSig s (S.TmPos p e) = S.TmPos p <$> inferFromSig s e
    inferFromSig s (S.TmOpen e1 e2) = S.TmOpen e1 <$> inferFromSig s e2
    inferFromSig (S.TyRcd xs) r@(S.TmRcd (S.RcdField o l Nil (Left e) : Nil)) =
      case last $ filterRcd (_ == l) xs of
        Just (S.RcdTy _ ty _) -> do
          e' <- inferFromSig ty e
          pure $ S.TmRcd (singleton (S.RcdField o l Nil (Left e')))
        _ -> pure r
    inferFromSig (S.TyRcd xs)
        (S.TmRcd (S.DefaultPattern pat@(S.MethodPattern _ label _ _) : Nil)) =
      S.TmRcd <$> for (filterRcd (_ `notElem` patterns label) xs)
        \(S.RcdTy l ty _) -> do
          let params /\ ty' = paramsAndInnerTy ty
          e <- inferFromSig ty' (desugarMP pat)
          pure $ S.RcdField false l params (Left e)
      where patterns :: Label -> Array Label
            patterns l = patternsFromRcd (S.TmMerge S.Neutral (fromMaybe S.TmUnit me1) ne2) l
            patternsFromRcd :: S.Tm -> Label -> Array Label
            patternsFromRcd (S.TmPos _ e) l = patternsFromRcd e l
            patternsFromRcd (S.TmOpen _ e) l = patternsFromRcd e l
            patternsFromRcd (S.TmRcd (S.RcdField _ l' _ (Left e) : Nil)) l =
              if innerLabel e == l then [l'] else []
            patternsFromRcd (S.TmRcd (S.DefaultPattern _ : Nil)) _ = []
            patternsFromRcd (S.TmRcd fields) l =
              foldl (\acc x -> acc <> patternsFromRcd (S.TmRcd (singleton (desugarField x))) l)
                    [] fields
            patternsFromRcd (S.TmMerge _ e1 e2) l =
              patternsFromRcd e1 l <> patternsFromRcd e2 l
            patternsFromRcd _ _ = []
            innerLabel :: S.Tm -> Label
            innerLabel (S.TmPos _ e) = innerLabel e
            innerLabel (S.TmOpen _ e) = innerLabel e
            innerLabel (S.TmAbs _ e) = innerLabel e
            innerLabel (S.TmTrait _ _ _ e) = innerLabel e
            innerLabel (S.TmRcd (S.RcdField _ l _ _ : Nil)) = l
            innerLabel _ = "$nothing"
            paramsAndInnerTy :: S.Ty -> S.TmParamList /\ S.Ty
            paramsAndInnerTy (S.TyArrow targ tret) =
              let params /\ ty = paramsAndInnerTy tret in
              (S.TmParam "_" (Just targ) : params) /\ ty
            paramsAndInnerTy ty = Nil /\ ty
    inferFromSig s@(S.TyRcd _) (S.TmRcd xs) =
      inferFromSig s (foldl1 (S.TmMerge S.Neutral)
                             (xs <#> \x -> S.TmRcd (singleton (desugarField x))))
    inferFromSig s (S.TmMerge bias e1 e2) =
      S.TmMerge bias <$> inferFromSig s e1 <*> inferFromSig s e2
    inferFromSig (S.TyArrow targ tret) (S.TmAbs (S.TmParam x mt : Nil) e) =
      S.TmAbs (singleton (S.TmParam x (mt <|> Just targ))) <$> inferFromSig tret e
    inferFromSig (S.TyArrow targ tret) (S.TmAbs (S.NamedParams fields true : Nil) e) = do
      e' <- inferFromSig tret e
      fields' <- expandWildcard (combineRcd targ) (getLabel <$> fields)
      pure $ S.TmAbs (singleton (S.NamedParams (fields <> fields') false)) e'
      where getLabel :: S.NamedField -> Label
            getLabel (S.RequiredField l _) = l
            getLabel (S.OptionalField l _) = l
            expandWildcard :: S.RcdTyList -> List Label -> Typing (List S.NamedField)
            expandWildcard Nil _ = pure Nil
            expandWildcard (S.RcdTy l ty opt : ts) ls = do
              fs <- expandWildcard ts ls
              if l `elem` ls then pure fs
              else if not opt then pure $ S.RequiredField l ty : fs
              else throwTypeError $ "default value for optional argument" <+>
                                    show l <+> "not found"
    inferFromSig s (S.TmAbs xs e) =
      inferFromSig s (foldr (\x acc -> S.TmAbs (singleton x) acc) e xs)
    inferFromSig (S.TyTrait ti to) (S.TmTrait (Just (self' /\ mt)) sig' e1 e2) = do
      e1' <- traverse (inferFromSig to) e1
      e2' <- inferFromSig to e2
      pure $ S.TmTrait (Just (self' /\ (mt <|> ti))) sig' e1' e2'
    inferFromSig s@(S.TyTrait _ _) (S.TmTrait Nothing sig' e1 e2) =
      inferFromSig s (S.TmTrait (Just ("$self" /\ Nothing)) sig' e1 e2)
    inferFromSig (S.TyForall ((a /\ td) : as) ty) (S.TmTAbs ((a' /\ td') : Nil) e) =
      S.TmTAbs (singleton (a' /\ (td' <|> td))) <$> inferFromSig ty' e
      where ty' = (if as == Nil then identity else S.TyForall as)
                  (S.tySubst a (S.TyVar a') ty)
    inferFromSig s (S.TmTAbs xs e) =
      inferFromSig s (foldr (\x acc -> S.TmTAbs (singleton x) acc) e xs)
    inferFromSig _ e = pure e
    combineRcd :: S.Ty -> S.RcdTyList
    combineRcd (S.TyAnd (S.TyRcd xs) (S.TyRcd ys)) = xs <> ys
    combineRcd (S.TyAnd l (S.TyRcd ys)) = combineRcd l <> ys
    combineRcd (S.TyAnd (S.TyRcd xs) r) = xs <> combineRcd r
    combineRcd (S.TyAnd l r) = combineRcd l <> combineRcd r
    combineRcd (S.TyRcd rcd) = rcd
    combineRcd _ = Nil
    filterRcd :: (Label -> Boolean) -> S.RcdTyList -> S.RcdTyList
    filterRcd f = filter \(S.RcdTy l _ _) -> f l
    override :: C.Ty -> S.Tm -> C.Ty
    override ty e = let ls = selectOverride e in
      if null ls then ty else removeOverride ty ls
      where selectOverride :: S.Tm -> Array Label
            selectOverride (S.TmPos _ e0) = selectOverride e0
            selectOverride (S.TmOpen _ e0) = selectOverride e0
            selectOverride (S.TmMerge _ e1 e2) = selectOverride e1 <> selectOverride e2
            -- TODO: only override the inner field if it's a method pattern
            selectOverride (S.TmRcd (S.RcdField true l _ _ : Nil)) = [l]
            selectOverride _ = []
            -- TODO: make sure every field overrides some field in super-trait
            removeOverride :: C.Ty -> Array Label -> C.Ty
            removeOverride (C.TyAnd t1 t2) ls =
              let t1' = removeOverride t1 ls
                  t2' = removeOverride t2 ls in
              case t1', t2' of
                C.TyTop, C.TyTop -> C.TyTop
                C.TyTop, _       -> t2'
                _,       C.TyTop -> t1'
                _,       _       -> C.TyAnd t1' t2'
            removeOverride (C.TyRcd l _) ls | l `elem` ls = C.TyTop
            removeOverride typ _ = typ
infer (S.TmTrait (Just (self /\ Nothing)) sig e1 e2) =
  infer $ S.TmTrait (Just (self /\ Just S.TyTop)) sig e1 e2
infer (S.TmTrait self sig e1 e2) =
  let xt = case self of Just (x /\ t) -> x /\ (t <|> sig)
                        Nothing -> "$self" /\ Nothing in
  infer $ S.TmTrait (Just xt) (sig <|> Just S.TyTop) e1 e2
infer (S.TmNew e) = do
  e' /\ t <- infer e
  case t of
    C.TyArrow ti to true ->
      if to <: ti then
        pure $ C.TmFix "$self" (C.TmApp e' (C.TmVar "$self") true) to /\ to
      else throwTypeError $ "input type is not a supertype of output type in" <+>
                            "Trait<" <+> show ti <+> "=>" <+> show to <+> ">"
    _ -> throwTypeError $ "new expected a trait, but got" <+> show t
infer (S.TmForward e1 e2) = do
  e1' /\ t1 <- infer e1
  e2' /\ t2 <- infer e2
  case t1 of
    C.TyArrow ti to true ->
      if t2 <: ti then pure $ C.TmApp e1' e2' true /\ to
      else throwTypeError $ "expected to forward to a subtype of" <+> show ti <>
                            ", but got" <+> show t2
    _ -> throwTypeError $ "expected to forward from a trait, but got" <+> show t1
infer (S.TmExclude e te) = do
  e' /\ t <- infer e
  te' <- transform te
  -- `check` helps to make sure `l` was present in `e` before exclusion,
  -- since the field removal `e \ l` desugars to `e \\ {l : Bot}`
  let check = case te' of C.TyRcd l C.TyBot -> checkLabel l
                          _ -> const $ pure unit
  case t of
    C.TyArrow ti to true -> do
      check to
      d <- tyDiff to te'
      let t' = C.TyArrow ti d true
      pure $ C.TmAnno e' t' /\ t'
    _ -> do
      check t
      d <- tyDiff t te'
      pure $ C.TmAnno e' d /\ d
  where checkLabel :: Label -> C.Ty -> Typing Unit
        checkLabel l (C.TyAnd t1 t2) = checkLabel l t1 <|> checkLabel l t2
        checkLabel l (C.TyRcd l' _) | l == l' = pure unit
        checkLabel l _ = throwTypeError $ "label" <+> show l <+> "is absent in" <+> show e
infer (S.TmRemoval e l) = do
  infer $ S.TmExclude e (S.TyRcd (singleton (S.RcdTy l S.TyBot false)))
infer (S.TmDiff e1 e2) = do
  e1' /\ t1 <- infer e1
  _ /\ t2 <- infer e2
  case t1, t2 of
    C.TyArrow ti to1 true, C.TyArrow _ to2 true -> do
      d <- tyDiff to1 to2
      pure $ trait "$self" (C.TmAnno (C.TmApp e1' (C.TmVar "$self") true) d) ti d
    _, _ -> do
      d <- tyDiff t1 t2
      pure $ C.TmAnno e1' d /\ d
infer (S.TmRename e old new) = do
  _ /\ t <- infer e
  case t of
    -- TODO: compiled code does not terminate because (e1^e2) is no more lazy
    C.TyArrow ti _ true ->
      case selectLabel ti old of
        Just tl -> do
          -- e [old <- new] := trait [self] =>
          --   let super = self [new <- old] in
          --   (e ^ super) [old <- new]
          let super = S.TmRename (S.TmVar "$self") new old
              body = S.TmRename (S.TmForward e super) old new
          tself <- C.TyAnd (C.TyRcd new tl) <$> tyDiff ti (C.TyRcd old C.TyBot)
          ret /\ tret <- addTmBind "$self" tself $ infer body
          pure $ trait "$self" ret tself tret
        Nothing -> do
          -- e [old <- new] := trait [self] => (e ^ self) [old <- new]
          let body = (S.TmRename (S.TmForward e (S.TmVar "$self")) old new)
          ret /\ tret <- addTmBind "$self" ti $ infer body
          pure $ trait "$self" ret ti tret
    _ ->
      -- e [old <- new] := e \ old , {new = e.old}
      infer $ S.TmMerge S.Neutral (S.TmRemoval e old)
        (S.TmRcd (singleton (S.RcdField false new Nil (Left (S.TmPrj e old)))))
infer (S.TmFold t e) = do
  t' <- transformTyRec t
  e' /\ t'' <- infer e
  if t'' <: C.unfold t' then pure $ C.TmFold t' e' /\ t'
  else throwTypeError $ "cannot fold" <+> show e <+> "to" <+> show t
infer (S.TmUnfold t e) = do
  t' <- transformTyRec t
  e' /\ t'' <- infer e
  if t'' <: t' then pure $ C.TmUnfold t' e' /\ C.unfold t'
  else throwTypeError $ "cannot unfold" <+> show e <+> "to" <+> show t
infer (S.TmRef e) = do
  e' /\ t <- infer e
  pure $ C.TmRef e' /\ C.TyRef t
infer (S.TmDeref e) = do
  e' /\ t <- infer e
  case t of C.TyRef t' -> pure $ C.TmDeref e' /\ t'
            _ -> throwTypeError $ "cannot dereference" <+> show t
infer (S.TmAssign e1 e2) = do
  e1' /\ t1 <- infer e1
  case t1 of C.TyRef t1' -> do e2' /\ t2 <- infer e2
                               if t2 <: t1' then pure $ C.TmAssign e1' e2' /\ C.TyUnit
                               else throwTypeError $ "assigned type" <+> show t2 <+>
                                                     "is not a subtype of" <+> show t1'
             _ -> throwTypeError $ "assignment expected a reference type, but got" <+> show t1
infer (S.TmSeq e1 e2) = do
  e1' /\ t1 <- infer e1
  case t1 of C.TyUnit -> do e2' /\ t2 <- infer e2
                            pure $ letIn "_" e1' t1 e2' t2 /\ t2
             _ -> throwTypeError $ "sequencing expected a unit type, but got" <+> show t1
infer (S.TmToString e) = do
  e' /\ t <- infer e
  if t == C.TyInt || t == C.TyDouble || t == C.TyString || t == C.TyBool
  then pure $ C.TmToString e' /\ C.TyString
  else throwTypeError $ "cannot show" <+> show t
infer (S.TmArray arr) = do
  if null arr then
    pure $ C.TmArray C.TyBot [] /\ C.TyArray C.TyBot
  else do
    ets <- traverse infer arr
    let es /\ ts = unzip ets
        t = unsafeFromJust $ head ts
    if all (_ === t) ts then pure $ C.TmArray t es /\ C.TyArray t
    else throwTypeError $ "elements of an array should all have the same type" <>
                          ", but got" <+> show (S.TmArray arr)
infer (S.TmDoc doc) = localPos f $ infer doc
  where f (Pos p e _) = Pos p e true
        f UnknownPos = UnknownPos
-- TODO: save original terms instead of desugared ones
infer (S.TmPos p e) = localPos f $ infer e
  where f (Pos _ _ inDoc) = Pos p e inDoc
        f UnknownPos = Pos p e false

inferRec :: Name -> S.Tm -> S.Ty -> Typing (C.Tm /\ C.Ty)
inferRec x e t = do
  t' <- transform t
  e' /\ t1 <- addTmBind x t' $ infer e
  if t1 <: t' then pure $ (if t1 === t' then e' else C.TmAnno e' t') /\ t'
  else throwTypeError $
    "annotated" <+> show t <+> "is not a supertype of inferred" <+> show t1

checkDef :: S.Def -> Checking Unit
checkDef (S.TyDef def a sorts params t) = do
  forbidDup <- gets (_.forbidDup)
  aliases <- gets (_.tyAliases)
  if forbidDup && isJust (lookup a aliases) then
    throwError $ TypeError ("type" <+> show a <+> "has already been defined") UnknownPos
  else case def of
    S.TypeAlias -> do
      ctx <- gets fromState
      case runTyping (addSorts $ addTyBinds $ transformTyDef t) ctx of
        Left err -> throwError err
        Right t' -> modify_ \st -> st { tyAliases = (a /\ sig t') : st.tyAliases }
    S.Interface -> do
      ctx <- gets fromState
      case runTyping (addSorts $ addTyBinds $ addTyBind a C.TyTop $ transformTyDef t) ctx of
        Left err -> throwError err
        Right t' -> modify_ \st -> st { tyAliases = (a /\ sig (S.TyRec a t')) : st.tyAliases }
                                                -- TODO: S.TyRec a (sig t')
    S.InterfaceExtends super -> do
      checkDef $ S.TyDef S.Interface (a <> "_") sorts params (S.tySubst a (S.TyVar (a <> "_")) t)
      let self = S.TyVar (a <> "_") # withSorts # withParams
      checkDef $ S.TyDef S.TypeAlias a sorts params (S.TyAnd super self)
  where
    dualSorts :: List (Name /\ Name)
    dualSorts = sorts <#> \sort -> sort /\ (sort <> "_")
    addSorts :: forall a. Typing a -> Typing a
    addSorts typing = foldr (uncurry addSort) typing dualSorts
    addTyBinds :: forall a. Typing a -> Typing a
    addTyBinds typing = foldr (flip addTyBind C.TyTop) typing params
    sig :: S.Ty -> S.Ty
    sig t' = foldr (uncurry S.TySig) (foldr S.TyAbs t' params) dualSorts    
    withSorts :: S.Ty -> S.Ty
    withSorts t' = let sort = S.TyVar >>> flip S.TySort Nothing in
                   foldl (S.TyApp >>> (sort >>> _)) t' sorts
    withParams :: S.Ty -> S.Ty
    withParams t' = foldl (S.TyApp >>> (S.TyVar >>> _)) t' params
checkDef (S.TmDef x Nil Nil mt e) = do
  forbidDup <- gets (_.forbidDup)
  bindings <- gets (_.tmBindings)
  if forbidDup && isJust (lookup x bindings) then
    throwError $ TypeError ("term" <+> show x <+> "has already been defined") UnknownPos
  else do
    ctx <- gets fromState
    let typing = case mt of Just t -> inferRec x e t
                            Nothing -> infer e
    case runTyping typing ctx of
      Left err -> throwError err
      Right (e' /\ t') ->
        let e1 = if isJust mt then C.TmFix x e' t' else e'
            f e2 = C.TmDef x e1 e2 in
        modify_ \st -> st { tmBindings = (x /\ t' /\ f) : st.tmBindings }
checkDef (S.TmDef x tyParams tmParams Nothing e) =
  checkDef $ S.TmDef x Nil Nil Nothing (S.TmTAbs tyParams (S.TmAbs tmParams e))
checkDef (S.TmDef x tyParams tmParams (Just t) e) =
  checkDef $ S.TmDef x Nil Nil (Just t') (S.TmTAbs tyParams (S.TmAbs tmParams e))
  where t' = tyOfParams tyParams tmParams t

checkProg :: S.Prog -> Checking (C.Tm /\ C.Ty)
checkProg (S.Prog defs e) = do
  traverse_ checkDef defs
  ctx <- gets fromState
  case runTyping (infer e) ctx of
    Left err -> throwError err
    Right (e' /\ t) -> pure $ C.TmMain e' /\ t

distApp :: C.Ty -> Either C.Ty C.Ty -> Typing C.Ty
distApp (C.TyArrow targ tret _) (Left t) | t <: targ = pure tret
                                         | otherwise = throwTypeError $
  "expected the argument type to be a subtype of the parameter type, but got" <+>
  show t <+> "and" <+> show targ
distApp (C.TyForall a td t) (Right ta) = disjoint ta td $> C.tySubst a ta t
distApp (C.TyAnd t1 t2) t = do
  t1' <- distApp t1 t
  t2' <- distApp t2 t
  pure $ C.TyAnd t1' t2'
distApp t _ = throwTypeError $ "expected an applicable type, but got" <+> show t

disjoint :: C.Ty -> C.Ty -> Typing Unit
disjoint t _ | isTopLike t = pure unit
disjoint _ t | isTopLike t = pure unit
disjoint (C.TyArrow _ t1 _) (C.TyArrow _ t2 _) = disjoint t1 t2
disjoint (C.TyAnd t1 t2) t3 = disjoint t1 t3 *> disjoint t2 t3
disjoint t1 (C.TyAnd t2 t3) = disjoint (C.TyAnd t2 t3) t1
disjoint (C.TyRcd l1 t1) (C.TyRcd l2 t2) | l1 == l2  = disjoint t1 t2
                                         | otherwise = pure unit
disjoint (C.TyVar a) (C.TyVar b) =
  disjointVar a (C.TyVar b) <|> disjointVar b (C.TyVar a)
disjoint (C.TyVar a) t = disjointVar a t
disjoint t (C.TyVar a) = disjointVar a t
disjoint (C.TyForall a1 td1 t1) (C.TyForall a2 td2 t2) =
  disjointTyBind a1 t1 a2 t2 (C.TyAnd td1 td2)
disjoint (C.TyRec a1 t1) (C.TyRec a2 t2) = disjointTyBind a1 t1 a2 t2 C.TyBot
disjoint t1 t2 | t1 /= t2 && t1 /= C.TyBot && t2 /= C.TyBot = pure unit
               | otherwise = throwTypeError $
  "expected two disjoint types, but got" <+> show t1 <+> "and" <+> show t2

disjointVar :: Name -> C.Ty -> Typing Unit
disjointVar a t = do
  mt' <- lookupTyBind a
  case mt' of
    Just t' -> if t' <: t then pure unit else throwTypeError $
      "type variable" <+> show a <+> "is not disjoint from" <+> show t
    Nothing -> throwTypeError $ "type variable" <+> show a <+> "is undefined"

disjointTyBind :: Name -> C.Ty -> Name -> C.Ty -> C.Ty -> Typing Unit
disjointTyBind a1 t1 a2 t2 td = addTyBind freshName td $
  disjoint (C.tySubst a1 freshVar t1) (C.tySubst a2 freshVar t2)
  where freshName = a1 <> " or " <> a2
        freshVar = C.TyVar freshName

letIn :: Name -> C.Tm -> C.Ty -> C.Tm -> C.Ty -> C.Tm
letIn x e1 t1 e2 t2 = C.TmApp (C.TmAbs x e2 t1 t2 false false) e1 false

trait :: Name -> C.Tm -> C.Ty -> C.Ty -> C.Tm /\ C.Ty
trait x e targ tret = C.TmAbs x e targ tret false isTrait /\ C.TyArrow targ tret true
  where isTrait = not $ isTopLike targ  -- skip traits whose self-type is top-like 

desugarMP :: S.MethodPattern -> S.Tm
desugarMP (S.MethodPattern self l p e) =
  S.TmTrait self Nothing Nothing (S.TmRcd (singleton (S.RcdField false l p (Left e))))

desugarField :: S.RcdField -> S.RcdField
-- TODO: override inner traits instead of outer ones
desugarField (S.RcdField o l p f) =
  S.RcdField o l Nil $ Left $ S.TmAbs p $ either identity desugarMP f
-- desugaring of default patterns is done in `inferFromSig`
desugarField def@(S.DefaultPattern _) = def

tyOfParams :: S.TyParamList -> S.TmParamList -> S.Ty -> S.Ty
tyOfParams tyParams tmParams retTy =
  S.TyForall tyParams (foldr S.TyArrow retTy (tyOfParam <$> tmParams))
  where tyOfParam :: S.TmParam -> S.Ty
        tyOfParam (S.TmParam _ (Just ty)) = ty
        tyOfParam (S.TmParam _ Nothing) = S.TyTop  -- unsupported type inference
        tyOfParam (S.NamedParams fields false) = S.TyRcd (tyOfField <$> fields)
        tyOfParam (S.NamedParams _ true) = S.TyTop -- unsupported type inference
        tyOfField :: S.NamedField -> S.RcdTy
        tyOfField (S.RequiredField l t) = S.RcdTy l t false
        -- TODO: infer the type of the default value `e`
        -- This cannot be done now because `infer` returns `C.Ty` instead of `S.Ty`
        tyOfField (S.OptionalField l _) = S.RcdTy l S.TyBot true

transformTyRec :: S.Ty -> Typing C.Ty
transformTyRec t = do
  t' <- transform t
  case t' of C.TyRec _ _ -> pure t'
             _ -> throwTypeError $
               "fold/unfold expected a recursive type, but got" <+> show t

collectLabels :: C.Ty -> Set.Set Label
collectLabels (C.TyAnd t1 t2) = Set.union (collectLabels t1) (collectLabels t2)
collectLabels (C.TyRcd l _) = Set.singleton l
collectLabels _ = Set.empty

selectLabel :: C.Ty -> Label -> Maybe C.Ty
selectLabel (C.TyAnd t1 t2) l =
  case selectLabel t1 l, selectLabel t2 l of
    Just t1', Just t2' -> Just (C.TyAnd t1' t2')
    Just t1', Nothing  -> Just t1'
    Nothing,  Just t2' -> Just t2'
    Nothing,  Nothing  -> Nothing
selectLabel (C.TyRcd l' t) l | l == l' = Just t
selectLabel _ _ = Nothing

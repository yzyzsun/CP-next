module Language.CP.Transform where

import Prelude

import Control.Alt ((<|>))
import Data.Bitraversable (rtraverse)
import Data.List (List(..), foldr)
import Data.Maybe (Maybe(..))
import Data.Traversable (for, traverse)
import Data.Tuple (fst, uncurry)
import Data.Tuple.Nested (type (/\), (/\))
import Language.CP.Context (Typing, addTyBind, lookupSort, lookupTyAlias, lookupTyBind, throwTypeError)
import Language.CP.Syntax.Core as C
import Language.CP.Syntax.Source as S
import Language.CP.TypeDiff (tyDiff)
import Language.CP.Util (foldl1, isCapitalized, (<+>))

transform :: S.Ty -> Typing C.Ty
transform = expand >=> translate

transform' :: S.Ty -> Typing (C.Ty /\ S.Ty)
transform' t = do
  t' <- expand t
  t'' <- translate t'
  pure $ t'' /\ t'

translate :: S.Ty -> Typing C.Ty
translate (S.TyRcd Nil) = pure C.TyTop
translate (S.TyRcd xs) = foldl1 C.TyAnd <$> for xs \(S.RcdTy l t opt) ->
  C.TyRcd l <$> translate t <@> opt
translate (S.TyForall xs t) =
  foldr (uncurry C.TyForall) <$> translate t <*>
    traverse (rtraverse disjointness) xs
  where disjointness :: Maybe S.Ty -> Typing C.Ty
        disjointness (Just s) = translate s
        disjointness Nothing  = pure C.TyTop
translate (S.TyDiff t1 t2) = do
  t1' <- translate t1
  t2' <- translate t2
  tyDiff t1' t2'

translate S.TyInt    = pure C.TyInt
translate S.TyDouble = pure C.TyDouble
translate S.TyString = pure C.TyString
translate S.TyBool   = pure C.TyBool
translate S.TyUnit   = pure C.TyUnit
translate S.TyTop    = pure C.TyTop
translate S.TyBot    = pure C.TyBot
translate (S.TyAnd t1 t2) = C.TyAnd <$> translate t1 <*> translate t2
translate (S.TyArrow t1 t2) = C.TyArrow <$> translate t1 <*> translate t2 <@> false
translate (S.TyVar a) = pure $ C.TyVar a
translate (S.TyRec a t) = C.TyRec a <$> translate t
translate (S.TyRef t) = C.TyRef <$> translate t
translate (S.TyTrait Nothing to) = translate to >>= \to' -> pure $ C.TyArrow to' to' true
translate (S.TyTrait (Just ti) to) =
  C.TyArrow <$> translate ti <*> translate to <@> true
translate (S.TyArray t) = C.TyArray <$> translate t
translate t@(S.TyAbs _ _) = throwTypeError $ "expected a proper type, but got" <+> show t
translate t@(S.TySig _ _ _) = throwTypeError $ "expected a proper type, but got" <+> show t
translate t = throwTypeError $ "expected an expanded type, but got" <+> show t

-- We don't need to check disjointness in the process of type expansion,
-- so a placeholder of core types will be added to TyBindEnv.
someTy :: C.Ty
someTy = C.TyTop

-- type-level beta-reduction is also done here
expand :: S.Ty -> Typing S.Ty
expand (S.TyArrow t1 t2) = S.TyArrow <$> expand t1 <*> expand t2
expand (S.TyAnd t1 t2) = S.TyAnd <$> expand t1 <*> expand t2
expand (S.TyRcd xs) = S.TyRcd <$> for xs \(S.RcdTy l t opt) ->
  S.RcdTy l <$> expand t <@> opt
expand (S.TyVar a) = do
  mtd <- lookupTyBind a
  ms <- lookupSort a
  case void mtd <|> void ms of
    Just _ -> pure $ S.TyVar a
    Nothing -> do
      mt <- lookupTyAlias a
      case mt of
        Just t -> expand t
        Nothing -> throwTypeError $ "type variable" <+> show a <+> "is undefined"
expand (S.TyForall xs t) =
  S.TyForall <$> traverse (rtraverse (traverse expand)) xs <*>
  foldr (\x s -> addTyBind (fst x) someTy s) (expand t) xs
expand (S.TyRec a t) = S.TyRec a <$> addTyBind a someTy (expand t)
expand (S.TyRef t) = S.TyRef <$> expand t
expand (S.TyApp t1 t2) = do
  t1' <- expand t1
  t2' <- expand t2
  case t1' of
    S.TyAbs a t -> pure $ S.tySubst a t2' t
    S.TySig a b t ->
      case t2' of
        S.TySort ti (Just to) -> do
          -- Here first substitute a and then b (i.e. #a) because
          -- some TyVar may be wrongly captured by a but impossible by #a.
          pure $ S.tySubst b to (S.tySubst a ti t)
        _ -> throwTypeError $ "sig instantiation expected a sort, but got" <+> show t2
    _ -> throwTypeError $  "expected an applicable type, but got" <+> show t1
expand (S.TyAbs a t) = addTyBind a someTy $ S.TyAbs a <$> expand t
expand (S.TyTrait ti to) = S.TyTrait <$> traverse expand ti <*> expand to
expand (S.TySort ti to) = do
  ti' <- expand ti
  mto <- traverse expand to
  case mto of
    Just to' -> pure $ S.TySort (S.TyAnd ti' to') (Just to')
    Nothing -> case ti' of
      S.TyVar a -> do
        mb <- lookupSort a
        case mb of Just b -> pure $ S.TySort ti' (Just (S.TyVar b))
                   Nothing -> pure $ S.TySort ti' (Just ti')
      _ -> pure $ S.TySort ti' (Just ti')
expand (S.TyArray t) = S.TyArray <$> expand t
expand (S.TyDiff t1 t2) = S.TyDiff <$> expand t1 <*> expand t2
expand t = pure t

-- If a type declaration is parametrized with sorts,
-- the input/output occurrences should be distinguished.
transformTyDef :: S.Ty -> Typing S.Ty
transformTyDef = expand >=> distinguish false true

distinguish :: Boolean -> Boolean -> S.Ty -> Typing S.Ty
distinguish isCtor isOut (S.TyArrow t1 t2) =
  S.TyArrow <$> distinguish isCtor (not isOut) t1 <*> distinguish isCtor isOut t2
distinguish isCtor isOut (S.TyAnd t1 t2) =
  S.TyAnd <$> distinguish isCtor isOut t1 <*> distinguish isCtor isOut t2
distinguish _ isOut (S.TyRcd xs) = S.TyRcd <$> for xs \(S.RcdTy l t opt) ->
  S.RcdTy l <$> distinguish (isCapitalized l) isOut t <@> opt
distinguish isCtor true t@(S.TyVar a) = do
  mb <- lookupSort a
  case mb of Just b -> do if isCtor then pure $ S.TyTrait (Just t) (S.TyVar b)
                                    else pure $ S.TyVar b
             Nothing -> pure $ S.TyVar a
-- TODO: remove bound variable names from SortEnv
distinguish isCtor isOut (S.TyForall xs t) = S.TyForall <$>
  traverse (rtraverse (traverse (distinguish isCtor isOut))) xs <*>
  distinguish isCtor isOut t
distinguish isCtor isOut (S.TyRec a t) = S.TyRec a <$> distinguish isCtor isOut t
-- TODO: `t` in `Ref` should be invariant but `isOut` seems covariant here
distinguish isCtor isOut (S.TyRef t) = S.TyRef <$> distinguish isCtor isOut t
distinguish isCtor isOut (S.TyApp t1 t2) =
  S.TyApp <$> distinguish isCtor isOut t1 <*> distinguish isCtor isOut t2
-- TODO: remove bound variable names from SortEnv
distinguish isCtor isOut (S.TyAbs a t) = S.TyAbs a <$> distinguish isCtor isOut t
distinguish isCtor isOut (S.TyTrait ti to) = S.TyTrait <$>
  traverse (distinguish isCtor (not isOut)) ti <*> distinguish isCtor isOut to
distinguish isCtor isOut (S.TyArray t) = S.TyArray <$> distinguish isCtor isOut t
distinguish isCtor isOut (S.TyDiff t1 t2) = 
  S.TyDiff <$> distinguish isCtor isOut t1 <*> distinguish isCtor isOut t2
distinguish _ _ t = pure t

module Zord.Transform where

import Prelude

import Control.Alt ((<|>))
import Data.Bitraversable (rtraverse)
import Data.Char.Unicode (isUpper)
import Data.List (List(..), foldr)
import Data.Maybe (Maybe(..))
import Data.String.Unsafe (charAt)
import Data.Traversable (for, traverse)
import Data.Tuple (Tuple(..), fst, snd, uncurry)
import Zord.Context (Typing, addTyBind, lookupSort, lookupTyAlias, lookupTyBind, throwTypeError)
import Zord.Syntax.Common (foldl1, (<+>))
import Zord.Syntax.Core as C
import Zord.Syntax.Source as S

transform :: S.Ty -> Typing C.Ty
transform = expand >=> translate

-- do other stuff between type expansion and translation
duringTransformation ::
  forall a b. (S.Ty -> a -> b) -> Tuple S.Ty a -> Typing (Tuple C.Ty b)
duringTransformation f (Tuple t x) = do
  t' <- expand t
  let x' = f t' x
  t'' <- translate t'
  pure $ Tuple t'' x'

translate :: S.Ty -> Typing C.Ty
translate (S.TyRcd Nil) = pure C.TyTop
translate (S.TyRcd xs) =
  foldl1 C.TyAnd <$> for xs \x -> C.TyRcd (fst x) <$> translate (snd x)
translate (S.TyForall xs t) =
  foldr (uncurry C.TyForall) <$> translate t <*>
    traverse (rtraverse disjointness) xs
  where disjointness :: Maybe S.Ty -> Typing C.Ty
        disjointness (Just s) = translate s
        disjointness Nothing  = pure C.TyTop

translate S.TyInt    = pure C.TyInt
translate S.TyDouble = pure C.TyDouble
translate S.TyString = pure C.TyString
translate S.TyBool   = pure C.TyBool
translate S.TyTop    = pure C.TyTop
translate S.TyBot    = pure C.TyBot
translate (S.TyAnd t1 t2) = C.TyAnd <$> translate t1 <*> translate t2
translate (S.TyArr t1 t2) = C.TyArr <$> translate t1 <*> translate t2 <@> false
translate (S.TyVar a) = pure $ C.TyVar a
translate (S.TyTrait Nothing to) = C.TyArr C.TyTop <$> translate to <@> true
translate (S.TyTrait (Just ti) to) =
  C.TyArr <$> translate ti <*> translate to <@> true
translate (S.TyList t) = C.TyList <$> translate t
translate t@(S.TyAbs _ _) = throwTypeError $ show t <+> "is not a proper type"
translate t@(S.TySig _ _ _) = throwTypeError $ show t <+> "is not a proper type"
translate t = throwTypeError $ show t <+> "should have been expanded"

-- We don't need to check disjointness in the process of type expansion,
-- so a placeholder of core types will be added to TyBindEnv.
someTy :: C.Ty
someTy = C.TyTop

-- type-level beta-reduction is also done here
expand :: S.Ty -> Typing S.Ty
expand (S.TyArr t1 t2) = S.TyArr <$> expand t1 <*> expand t2
expand (S.TyAnd t1 t2) = S.TyAnd <$> expand t1 <*> expand t2
expand (S.TyRcd xs) = S.TyRcd <$> traverse (rtraverse expand) xs
expand (S.TyVar a) = do
  mtd <- lookupTyBind a
  ms <- lookupSort a
  case void mtd <|> void ms of
    Just unit -> pure $ S.TyVar a
    Nothing -> do
      mt <- lookupTyAlias a
      case mt of
        Just t -> expand t
        Nothing -> throwTypeError $ "type variable" <+> show a <+> "is undefined"
expand (S.TyForall xs t) =
  S.TyForall <$> traverse (rtraverse (traverse expand)) xs <*>
  foldr (\x s -> addTyBind (fst x) someTy s) (expand t) xs
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
        _ -> throwTypeError $
          "sig" <+> show t1' <+> "expected a sort, but got" <+> show t2'
    _ -> throwTypeError $ "type" <+> show t1' <+> "is not applicable"
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
expand (S.TyList t) = S.TyList <$> expand t
expand t = pure t

transformTyDef :: S.Ty -> Typing S.Ty
transformTyDef = expand >=> distinguish false true

distinguish :: Boolean -> Boolean -> S.Ty -> Typing S.Ty
distinguish isCtor isOut (S.TyArr t1 t2) =
  S.TyArr <$> distinguish isCtor (not isOut) t1 <*> distinguish isCtor isOut t2
distinguish isCtor isOut (S.TyAnd t1 t2) =
  S.TyAnd <$> distinguish isCtor isOut t1 <*> distinguish isCtor isOut t2
distinguish isCtor isOut (S.TyRcd xs) = S.TyRcd <$> for xs \(Tuple l t) ->
  Tuple l <$> distinguish (isUpper (charAt 0 l)) isOut t
distinguish isCtor true t@(S.TyVar a) = do
  mb <- lookupSort a
  case mb of Just b -> do if isCtor then pure $ S.TyTrait (Just t) (S.TyVar b)
                                    else pure $ S.TyVar b
             Nothing -> pure $ S.TyVar a
-- TODO: remove bound variable names from SortEnv
distinguish isCtor isOut (S.TyForall xs t) = S.TyForall <$>
  traverse (rtraverse (traverse (distinguish isCtor isOut))) xs <*>
  distinguish isCtor isOut t
distinguish isCtor isOut (S.TyApp t1 t2) =
  S.TyApp <$> distinguish isCtor isOut t1 <*> distinguish isCtor isOut t2
-- TODO: remove bound variable names from SortEnv
distinguish isCtor isOut (S.TyAbs a t) =
  S.TyAbs a <$> distinguish isCtor isOut t
distinguish isCtor isOut (S.TyTrait ti to) = S.TyTrait <$>
  traverse (distinguish isCtor (not isOut)) ti <*> distinguish isCtor isOut to
distinguish _ _ t = pure t

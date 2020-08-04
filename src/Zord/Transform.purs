module Zord.Transform where

import Prelude

import Data.Bitraversable (rtraverse)
import Data.List (List(..), foldr)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (fst, snd, uncurry)
import Zord.Context (Typing, addTyBind, lookupTyAlias, lookupTyBind, throwTypeError)
import Zord.Syntax.Common (foldl1, (<+>))
import Zord.Syntax.Core as C
import Zord.Syntax.Source as S

transform :: S.Ty -> Typing C.Ty
transform = expand >=> elaborate

elaborate :: S.Ty -> Typing C.Ty
elaborate (S.TyRcd Nil) = pure C.TyTop
elaborate (S.TyRcd xs) =
  foldl1 C.TyAnd <$> traverse (\x -> C.TyRcd (fst x) <$> elaborate (snd x)) xs
elaborate (S.TyForall xs t) =
  foldr (uncurry C.TyForall) <$> elaborate t <*>
    traverse (rtraverse disjointness) xs
  where disjointness :: Maybe S.Ty -> Typing C.Ty
        disjointness (Just s) = elaborate s
        disjointness Nothing  = pure C.TyTop

elaborate S.TyInt    = pure C.TyInt
elaborate S.TyDouble = pure C.TyDouble
elaborate S.TyString = pure C.TyString
elaborate S.TyBool   = pure C.TyBool
elaborate S.TyTop    = pure C.TyTop
elaborate S.TyBot    = pure C.TyBot
elaborate (S.TyAnd t1 t2) = C.TyAnd <$> elaborate t1 <*> elaborate t2
elaborate (S.TyArr t1 t2) = C.TyArr <$> elaborate t1 <*> elaborate t2 <@> false
elaborate (S.TyVar a) = pure $ C.TyVar a
elaborate (S.TyTrait (Just ti) to) =
  C.TyArr <$> elaborate ti <*> elaborate to <@> true
elaborate (S.TyTrait Nothing to) = C.TyArr C.TyTop <$> elaborate to <@> true
elaborate t@(S.TyAbs _ _) = throwTypeError $ show t <+> "is not a proper type"
elaborate t = throwTypeError $ show t <+> "should have been expanded"

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
  case mtd of
    Just _ -> pure $ S.TyVar a
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
  case t1' of S.TyAbs a t -> pure $ S.tySubst a t2' t
              _ -> throwTypeError $ "type" <+> show t1' <+> "is not applicable"
expand (S.TyAbs a t) = addTyBind a someTy $ S.TyAbs a <$> expand t
expand (S.TyTrait ti to) = S.TyTrait <$> traverse expand ti <*> expand to
expand t = pure t

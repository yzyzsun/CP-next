module Zord.Transform where

import Prelude

import Data.Bitraversable (rtraverse)
import Data.List (List(..), foldr)
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Data.Tuple (fst, snd)
import Partial.Unsafe (unsafeCrashWith)
import Zord.Context (Typing, addTyBind, lookupTyBind, throwTypeError)
import Zord.Syntax.Common (foldl1, (<+>))
import Zord.Syntax.Core as C
import Zord.Syntax.Source as S

transform :: S.Ty -> Typing C.Ty
transform t = elaborate <$> expand t

elaborate :: S.Ty -> C.Ty
elaborate (S.TyRcd Nil) = C.TyTop
elaborate (S.TyRcd xs) =
  foldl1 C.TyAnd (xs <#> \x -> C.TyRcd (fst x) (elaborate (snd x)))
elaborate (S.TyForall xs t) =
  foldr (\x s -> C.TyForall (fst x) (disjointness (snd x)) s) (elaborate t) xs
  where disjointness :: Maybe S.Ty -> C.Ty
        disjointness (Just s) = elaborate s
        disjointness Nothing  = C.TyTop

elaborate S.TyInt    = C.TyInt
elaborate S.TyDouble = C.TyDouble
elaborate S.TyString = C.TyString
elaborate S.TyBool   = C.TyBool
elaborate S.TyTop    = C.TyTop
elaborate S.TyBot    = C.TyBot
elaborate (S.TyAnd t1 t2) = C.TyAnd (elaborate t1) (elaborate t2)
elaborate (S.TyArr t1 t2) = C.TyArr (elaborate t1) (elaborate t2) false
elaborate (S.TyVar a) = C.TyVar a
elaborate (S.TyTrait (Just ti) to) = C.TyArr (elaborate ti) (elaborate to) true
elaborate (S.TyTrait Nothing to) = C.TyArr C.TyTop (elaborate to) true
elaborate t = unsafeCrashWith $
  "Zord.Transform.elaborate:" <+> show t <+> "should have been expanded"

-- type-level beta-reduction is also done here
expand :: S.Ty -> Typing S.Ty
expand (S.TyArr t1 t2) = S.TyArr <$> expand t1 <*> expand t2
expand (S.TyAnd t1 t2) = S.TyAnd <$> expand t1 <*> expand t2
expand (S.TyRcd xs) = S.TyRcd <$> traverse (rtraverse expand) xs
expand (S.TyVar a) = lookupTyBind a $> S.TyVar a
expand (S.TyForall xs t) = S.TyForall xs <$>
  -- TODO: add a separate context for kinding
  foldr (\x s -> addTyBind (fst x) C.TyTop s) (expand t) xs
expand (S.TyApp t1 t2) = do
  t1' <- expand t1
  t2' <- expand t2
  case t1' of S.TyAbs a t -> pure $ S.tySubst a t2' t
              _ -> throwTypeError $ "type" <+> show t1' <+> "is not applicable"
expand t@(S.TyAbs _ _) =
  throwTypeError $ "type" <+> show t <+> "is not well-formed"
expand (S.TyTrait ti to) = S.TyTrait <$> traverse expand ti <*> expand to
expand t = pure t

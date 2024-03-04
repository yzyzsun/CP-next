module Language.CP.TypeDiff where

import Prelude

import Control.Alt ((<|>))
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Language.CP.Context (Typing, lookupTyBind, throwTypeError)
import Language.CP.Subtyping (isTopLike, split)
import Language.CP.Syntax.Common (Name)
import Language.CP.Syntax.Core (Ty(..), tySubst)
import Partial.Unsafe (unsafeCrashWith)

tyDiff :: Ty -> Ty -> Typing Ty
tyDiff m s = simplify <$> diff m s
  where
    -- this algorithm does not depend on separate definitions of subtyping or disjointness
    diff :: Ty -> Ty -> Typing Ty
    diff t1 t2 | isTopLike t1 || isTopLike t2 = pure t1
    diff t1 t2 | Just (t3 /\ t4) <- split t1 =
      tyMerge t1 <$> diff t3 t2 <*> diff t4 t2
    diff t (TyAnd t1 t2) = (diff t t1 >>= \t' -> diff t' t2) <|>
                           (diff t t2 >>= \t' -> diff t' t1)
    diff TyBot TyBot = pure TyTop
    diff t TyBot = diff t t        -- should not precede left-split
    diff TyBot _ = throwDiffError  -- should not precede right-and
    diff t@(TyArrow targ1 tret1 b) (TyArrow targ2 tret2 _) = do
      dret <- diff tret1 tret2
      if dret == tret1 then pure t  -- disjoint (m * s)
      else do darg <- diff targ2 targ1
              if isTopLike darg  -- supertype (m :> s)
              then pure $ TyArrow targ1 dret b else throwDiffError
    diff t@(TyRcd l1 t1 b) (TyRcd l2 t2 _)
      | l1 == l2  = TyRcd l1 <$> diff t1 t2 <@> b
      | otherwise = pure t
    diff t@(TyForall a1 td1 t1) (TyForall a2 td2 t2) = do
      d <- diff t1 t2'
      if d == t1 then pure t  -- disjoint (m * s)
      else do dd <- diff td2 td1
              if isTopLike dd  -- supertype (m :> s)
              then pure $ TyForall a1 td1 d else throwDiffError
      where t2' = tySubst a2 (TyVar a1) t2
    diff (TyVar a1) (TyVar a2) | a1 == a2 = pure TyTop
    diff (TyVar a) t = disjointVar a t >>=
      if _ then pure $ TyVar a else throwDiffError
    diff t (TyVar a) = disjointVar a t >>=
      if _ then pure t else throwDiffError
    diff (TyArray t1) (TyArray t2) = TyArray <$> diff t1 t2
    -- TODO: recursive type difference
    diff (TyRec _ _) _ = throwDiffError
    diff _ (TyRec _ _) = throwDiffError
    diff (TyRef _) _ = throwDiffError
    diff _ (TyRef _) = throwDiffError
    diff (TyArray _) _ = throwDiffError
    diff _ (TyArray _) = throwDiffError
    diff t1 t2 | t1 == t2  = pure TyTop
               | otherwise = pure t1
    disjointVar :: Name -> Ty -> Typing Boolean
    disjointVar a t = lookupTyBind a >>= case _ of
      Just td -> isTopLike <$> diff t td
      Nothing -> pure false
    throwDiffError :: Typing Ty
    throwDiffError = throwTypeError $ "cannot subtract " <> show s <> " from " <> show m

tyMerge :: Ty -> Ty -> Ty -> Ty
tyMerge (TyAnd _ _) t1 t2 = TyAnd t1 t2
tyMerge (TyArrow targ tret b) (TyArrow targ1 t1 b1) (TyArrow targ2 t2 b2)
  | targ == targ1 && targ == targ2 && b == b1 && b == b2
  = TyArrow targ (tyMerge tret t1 t2) b
tyMerge (TyRcd l t b) (TyRcd l1 t1 b1) (TyRcd l2 t2 b2)
  | l == l1 && l == l2 && b == b1 && b == b2
  = TyRcd l (tyMerge t t1 t2) b
tyMerge (TyForall a td t) (TyForall a1 td1 t1) (TyForall a2 td2 t2)
  | a == a1 && a == a2 && td == td1 && td == td2
  = TyForall a td (tyMerge t t1 t2)
tyMerge t t1 t2 = unsafeCrashWith $ "CP.TypeDiff.tyMerge: " <>
  "cannot merge " <> show t1 <> " and " <> show t2 <> " according to " <> show t

simplify :: Ty -> Ty
simplify t | isTopLike t = TyTop
simplify t@(TyAnd t1 t2) = case isTopLike t1, isTopLike t2 of
  true,  true  -> TyTop
  true,  false -> t2
  false, true  -> t1
  false, false -> t
simplify (TyArrow targ tret b) = TyArrow targ (simplify tret) b
simplify (TyRcd l t b) = TyRcd l (simplify t) b
simplify (TyForall a td t) = TyForall a td (simplify t)
simplify (TyRec a t) = TyRec a (simplify t)
simplify (TyRef t) = TyRef (simplify t)
simplify (TyArray t) = TyArray (simplify t)
simplify t = t

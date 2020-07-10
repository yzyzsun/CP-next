module Zord.Subtyping where

import Prelude

import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..))
import Zord.Syntax (Ty(..))

subtype :: Ty -> Ty -> Boolean
subtype Bot _ = true
subtype _ t | isTopLike t = true
subtype t1 t2 | Just (Tuple t3 t4) <- split t2 = t1 <: t3 && t1 <: t4
subtype (Arr targ1 tret1) (Arr targ2 tret2) = targ2 <: targ1 && tret1 <: tret2
subtype (Intersect t1 t2) t3 = t1 <: t3 || t2 <: t3
subtype (Rec l1 t1) (Rec l2 t2) | l1 == l2 = t1 <: t2
subtype t1 t2 | t1 == t2  = true
              | otherwise = false

infix 4 subtype as <:

supertype :: Ty -> Ty -> Boolean
supertype = flip subtype

infix 4 supertype as :>

isTopLike :: Ty -> Boolean
isTopLike Top = true
isTopLike (Arr _ t) = isTopLike t
isTopLike (Intersect t1 t2) = isTopLike t1 && isTopLike t2
isTopLike (Rec _ t) = isTopLike t
isTopLike _ = false

split :: Ty -> Maybe (Tuple Ty Ty)
split (Intersect t1 t2) = Just $ Tuple t1 t2
split (Arr targ tret) = split tret >>= \(Tuple tret1 tret2) ->
  Just $ Tuple (Arr targ tret1) (Arr targ tret2)
split (Rec l t) = split t >>= \(Tuple t1 t2) ->
  Just $ Tuple (Rec l t1) (Rec l t2)
split _ = Nothing

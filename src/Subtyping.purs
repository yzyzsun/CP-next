module Zord.Subtyping where

import Prelude

import Zord.Syntax (Ty(..))

subtype :: Ty -> Ty -> Boolean
subtype _ Top = true
subtype _ (Arr _ t) | Top <: t = true
subtype (Arr targ1 tret1) (Arr targ2 tret2) = targ2 <: targ1 && tret1 <: tret2
subtype t1 (Intersect t2 t3) = t1 <: t2 && t1 <: t3
subtype (Intersect t1 t2) t3 = t1 <: t3 || t2 <: t3
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
isTopLike _ = false


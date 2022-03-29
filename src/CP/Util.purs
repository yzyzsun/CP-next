module Language.CP.Util where

import Prelude

import Data.CodePoint.Unicode (isUpper)
import Data.List (List(..), foldl, (:))
import Data.Maybe (Maybe(..))
import Data.String (codePointAt)
import Partial.Unsafe (unsafeCrashWith)

beside :: String -> String -> String
beside s1 s2 = s1 <> " " <> s2

infixr 5 beside as <+>

foldl1 :: forall a. (a -> a -> a) -> List a -> a
foldl1 _ Nil = unsafeCrashWith "foldl1: empty list"
foldl1 f (x : xs) = foldl f x xs

foldr1 :: forall a. (a -> a -> a) -> List a -> a
foldr1 _ Nil = unsafeCrashWith "foldr1: empty list"
foldr1 _ (x : Nil) = x
foldr1 f (x : xs) = f x (foldr1 f xs)

unsafeFromJust :: forall a. Maybe a -> a
unsafeFromJust Nothing = unsafeCrashWith "unsafeFromJust: unexpected Nothing"
unsafeFromJust (Just x) = x

isCapitalized :: String -> Boolean
isCapitalized = isUpper <<< unsafeFromJust <<< codePointAt 0

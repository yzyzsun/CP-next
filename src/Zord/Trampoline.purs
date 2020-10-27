module Zord.Trampoline where

import Prelude

data Trampoline a = Done a
                  | More (Unit -> Trampoline a)
                  | Bind (Trampoline a) (a -> Trampoline a)

runTrampoline :: forall a. Trampoline a -> a
runTrampoline (Done v) = v
runTrampoline (More k) = runTrampoline $ k unit
runTrampoline (Bind x f) = case x of
  Done v -> runTrampoline $ f v
  More k -> runTrampoline $ Bind (k unit) f
  Bind y g -> runTrampoline $ Bind y \v -> Bind (g v) f

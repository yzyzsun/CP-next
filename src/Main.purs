module Main where

import Prelude

import Data.Array (drop, length)
import Data.Traversable (for_)
import Effect (Effect)
import Effect.Ref (new)
import Language.CP.Context (initState)
import Node.Process (argv)
import REPL (compileFile, repl)

main :: Effect Unit
main = do
  args <- argv
  if length args <= 2 then repl
  else do
    state <- new initState
    for_ (drop 2 args) \arg ->
      compileFile arg state

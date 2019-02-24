{-# LANGUAGE DeriveTraversable #-}
module Elab.Name where

data Head a
  = Free a
  | Bound Int
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

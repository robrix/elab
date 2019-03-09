{-# LANGUAGE DeriveTraversable #-}
module Elab.Plicity where

data Plicity a
  = Im a
  | Ex a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

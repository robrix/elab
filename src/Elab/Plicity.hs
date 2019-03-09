{-# LANGUAGE DeriveTraversable #-}
module Elab.Plicity where

import Elab.Pretty

data Plicity a
  = Im a
  | Ex a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Pretty a => Pretty (Plicity a) where
  prettys (Im a) = showChar '{' . prettys a . showChar '}'
  prettys (Ex a) = showChar '(' . prettys a . showChar ')'

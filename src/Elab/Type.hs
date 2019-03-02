{-# LANGUAGE DeriveTraversable #-}
module Elab.Type where

import Elab.Name
import Elab.Stack

data Type a
  = Type
  | Lam (Type a) (Scope a)
  | Pi  (Type a) (Scope a)
  | Head a :$ Stack (Type a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope (Type a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

{-# LANGUAGE DeriveTraversable #-}
module Elab.Stack where

data Stack a = Nil | Stack a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 5 :>

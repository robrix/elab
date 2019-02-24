{-# LANGUAGE DeriveTraversable #-}
module Elab.Term where

data Term a
  = Free a
  | Bound Int
  | Lam (Scope a)
  | App (Term a) (Term a)
  | Type
  | Pi (Term a) (Scope a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope (Term a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

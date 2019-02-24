{-# LANGUAGE DeriveTraversable, LambdaCase #-}
module Elab.Term where

data Term a
  = Head (Head a)
  | Lam (Scope a)
  | App (Term a) (Term a)
  | Type
  | Pi (Term a) (Scope a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope (Term a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

data Head a
  = Free a
  | Bound Int
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

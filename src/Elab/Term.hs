module Elab.Term where

data Term a
  = Free a
  | Bound Int
  | Lam (Scope a)
  | App (Term a) (Term a)
  | Type
  | Pi (Term a) (Scope a)

newtype Scope a = Scope (Term a)

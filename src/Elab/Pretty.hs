module Elab.Pretty where

class Pretty a where
  prettys :: a -> ShowS

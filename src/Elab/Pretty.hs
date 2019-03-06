module Elab.Pretty where

class Pretty a where
  prettys :: a -> ShowS

pretty :: Pretty a => a -> String
pretty = ($ "") . prettys

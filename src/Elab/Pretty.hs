module Elab.Pretty where

import Text.Show

class Pretty a where
  prettys :: a -> ShowS

pretty :: Pretty a => a -> String
pretty = ($ "") . prettys

instance Pretty a => Pretty [a] where
  prettys = showListWith prettys

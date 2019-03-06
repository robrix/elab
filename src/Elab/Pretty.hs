module Elab.Pretty where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Text.Show

class Pretty a where
  prettys :: a -> ShowS

pretty :: Pretty a => a -> String
pretty = ($ "") . prettys

instance Pretty a => Pretty [a] where
  prettys = showListWith prettys

instance (Pretty k, Pretty v) => Pretty (Map.Map k v) where
  prettys = showListWith prettyPair . Map.toList
    where prettyPair (k, v) = prettys k . showString " => " . prettys v

instance Pretty a => Pretty (Set.Set a) where
  prettys = showListWith prettys . Set.toList

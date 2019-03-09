{-# LANGUAGE DeriveTraversable #-}
module Elab.Stack where

import Data.Foldable (toList)
import Elab.Pretty

data Stack a = Nil | Stack a :> a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixl 5 :>

instance Semigroup (Stack a) where
  as  <> Nil       = as
  Nil <> bs        = bs
  as  <> (bs :> b) = (as <> bs) :> b

instance Monoid (Stack a) where
  mempty = Nil
  mappend = (<>)

instance Pretty a => Pretty (Stack a) where
  prettys = prettys . toList

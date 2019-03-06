{-# LANGUAGE DeriveTraversable, FlexibleContexts, TypeOperators #-}
module Elab.Name where

import Control.Effect
import Control.Effect.Fresh
import Control.Effect.Reader
import Elab.Pretty

data Head a
  = Free a
  | Bound Int
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


data Name
  = Global String
  | Local  Gensym
  deriving (Eq, Ord, Show)


data Meta
  = Name Name
  | Meta Gensym
  deriving (Eq, Ord, Show)


data Gensym
  = Root String
  | Gensym :/ (String, Int)
  deriving (Eq, Ord, Show)

instance Pretty Gensym where
  prettys (Root s) = showString s
  prettys (root :/ (leaf, i)) = prettys root . showChar '.' . showString leaf . shows i

infixl 6 :/

(//) :: Gensym -> String -> Gensym
root // s = root :/ (s, 0)

infixl 6 //

gensym :: (Carrier sig m, Member Fresh sig, Member (Reader Gensym) sig) => String -> m Gensym
gensym s = (:/) <$> ask <*> ((,) s <$> fresh)


data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 6 :::

instance (Pretty a, Pretty b) => Pretty (a ::: b) where
  prettys (a ::: b) = prettys a . showString " : " . prettys b

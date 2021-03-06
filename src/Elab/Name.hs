{-# LANGUAGE DeriveTraversable, FlexibleContexts, TypeOperators #-}
module Elab.Name where

import Control.Effect
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Local)
import Elab.Pretty

data Head a
  = Free a
  | Bound Int
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Pretty a => Pretty (Head a) where
  prettys (Free a) = prettys a
  prettys (Bound i) = shows i


data Name
  = Global String
  | Local  Gensym
  deriving (Eq, Ord, Show)

instance Pretty Name where
  prettys (Global s) = showChar '$' . showString s
  prettys (Local n)  = showChar '_' . prettys n


data Meta
  = Name Name
  | Meta Gensym
  deriving (Eq, Ord, Show)

instance Pretty Meta where
  prettys (Name n) = prettys n
  prettys (Meta g) = showChar '@' . prettys g


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


data Incr a = Z | S a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

match :: Eq a => a -> a -> Incr a
match x y | x == y    = Z
          | otherwise = S y

subst :: a -> Incr a -> a
subst a Z     = a
subst _ (S a) = a

instance Pretty a => Pretty (Incr a) where
  prettys Z = showChar 'Z'
  prettys (S a) = showString "S " . prettys a

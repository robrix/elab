{-# LANGUAGE DeriveTraversable, FlexibleContexts #-}
module Elab.Name where

import Control.Effect
import Control.Effect.Fresh
import Control.Effect.Reader

data Head a
  = Free a
  | Bound Int
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


data Gensym
  = Root String
  | Gensym :/ (String, Int)

infixl 6 :/

(//) :: Gensym -> String -> Gensym
root // s = root :/ (s, 0)

infixl 6 //

gensym :: (Applicative m, Carrier sig m, Member Fresh sig, Member (Reader Gensym) sig) => String -> m Gensym
gensym s = (:/) <$> ask <*> ((,) s <$> fresh)

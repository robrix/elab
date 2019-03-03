{-# LANGUAGE DeriveTraversable, LambdaCase, TypeOperators #-}
module Elab.Type where

import Control.Monad (ap)
import Data.Foldable (foldl')
import Elab.Name
import Elab.Stack
import Prelude hiding (pi)

data Type a
  = Type
  | Lam          (Scope a)
  | Pi  (Type a) (Scope a)
  | Head a :$ Stack (Type a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope (Type a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)


data a ::: b = a ::: b
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infix 6 :::

lam :: Eq a => a -> Type a -> Type a
lam n b = Lam (bind n b)

lams :: (Eq a, Foldable t) => t a -> Type a -> Type a
lams names body = foldr lam body names

pi :: Eq a => a ::: Type a -> Type a -> Type a
pi (n ::: t) b = Pi t (bind n b)

pis :: (Eq a, Foldable t) => t (a ::: Type a) -> Type a -> Type a
pis names body = foldr pi body names

($$) :: Type a -> Type a -> Type a
Lam   b $$ v = instantiate v b
Pi  _ b $$ v = instantiate v b
n :$ vs $$ v = n :$ (vs :> v)
Type    $$ _ = error "illegal application of Type"

($$*) :: Foldable t => Type a -> t (Type a) -> Type a
v $$* sp = foldl' ($$) v sp


-- | Bind occurrences of a 'Name' in a 'Type' term, producing a 'Scope' in which the 'Name' is bound.
bind :: Eq a => a -> Type a -> Scope a
bind name = Scope . substIn (\ i v -> (:$ mempty) $ case v of
  Bound j -> Bound j
  Free  n -> if name == n then Bound i else Free n)

-- | Substitute a 'Type' term for the free variable in a given 'Scope', producing a closed 'Type' term.
instantiate :: Type a -> Scope a -> Type a
instantiate image (Scope b) = substIn (\ i v -> case v of
  Bound j -> if i == j then image else Bound j :$ mempty
  Free  n -> pure n) b

substIn :: (Int -> Head a -> Type b)
        -> Type a
        -> Type b
substIn var = go 0
  where go i (Lam (Scope b))  = Lam (Scope (go (succ i) b))
        go i (f :$ a)         = var i f $$* fmap (go i) a
        go _ Type             = Type
        go i (Pi t (Scope b)) = Pi (go i t) (Scope (go (succ i) b))


instance Applicative Type where
  pure a = Free a :$ mempty
  (<*>) = ap

instance Monad Type where
  a >>= f = substIn (const (\case
    Free a' -> f a'
    Bound i -> Bound i :$ mempty)) a

{-# LANGUAGE DeriveTraversable, LambdaCase, TypeOperators #-}
module Elab.Term where

import Control.Monad (ap)
import Elab.Name
import Prelude hiding (pi)

data Term a
  = Head (Head a)
  | Lam (Scope a)
  | Term a :$ Term a
  | Type
  | Pi (Term a) (Scope a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope (Term a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

lam :: Eq a => a -> Term a -> Term a
lam n b = Lam (bind n b)

lams :: (Eq a, Foldable t) => t a -> Term a -> Term a
lams names body = foldr lam body names

pi :: Eq a => a ::: Term a -> Term a -> Term a
pi (n ::: t) b = Pi t (bind n b)

pis :: (Eq a, Foldable t) => t (a ::: Term a) -> Term a -> Term a
pis names body = foldr pi body names


-- | Bind occurrences of a 'Name' in a 'Term' term, producing a 'Scope' in which the 'Name' is bound.
bind :: Eq a => a -> Term a -> Scope a
bind name = Scope . substIn (\ i v -> Head $ case v of
  Bound j -> Bound j
  Free  n -> if name == n then Bound i else Free n)

-- | Substitute a 'Term' term for the free variable in a given 'Scope', producing a closed 'Term' term.
instantiate :: Term a -> Scope a -> Term a
instantiate image (Scope b) = substIn (\ i v -> case v of
  Bound j -> if i == j then image else Head (Bound j)
  Free  n -> pure n) b

substIn :: (Int -> Head a -> Term b)
        -> Term a
        -> Term b
substIn var = go 0
  where go i (Head h)         = var i h
        go i (Lam (Scope b))  = Lam (Scope (go (succ i) b))
        go i (f :$ a)         = go i f :$ go i a
        go _ Type             = Type
        go i (Pi t (Scope b)) = Pi (go i t) (Scope (go (succ i) b))


instance Applicative Term where
  pure = Head . Free
  (<*>) = ap

instance Monad Term where
  a >>= f = substIn (const (\case
    Free a' -> f a'
    Bound i -> Head (Bound i))) a


identityT :: Term Name
identityT = pi (Local (Root "x") ::: Type) (pi (Local (Root "y") ::: pure (Local (Root "x"))) (pure (Local (Root "x"))))

identity :: Term Name
identity = lam (Local (Root "x")) (lam (Local (Root "y")) (pure (Local (Root "y"))))

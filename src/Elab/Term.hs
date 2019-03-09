{-# LANGUAGE DeriveTraversable, LambdaCase, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Elab.Term where

import Control.Monad (ap)
import Elab.Name
import Prelude hiding (pi)

data Term a
  = Var a
  | Lam (Scope a)
  | Term a :$ Term a
  | Type
  | Pi (Term a) (Scope a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

newtype Scope a = Scope (Term (Incr a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

lam :: Eq a => a -> Term a -> Term a
lam n b = Lam (Scope (match n <$> b))

lams :: (Eq a, Foldable t) => t a -> Term a -> Term a
lams names body = foldr lam body names

pi :: Eq a => a ::: Term a -> Term a -> Term a
pi (n ::: t) b = Pi t (Scope (match n <$> b))

pis :: (Eq a, Foldable t) => t (a ::: Term a) -> Term a -> Term a
pis names body = foldr pi body names


gfoldT :: forall m n b
       .  (forall a . m a -> n a)
       -> (forall a . n (Incr a) -> n a)
       -> (forall a . n a -> n a -> n a)
       -> (forall a . n a)
       -> (forall a . n a -> n (Incr a) -> n a)
       -> (forall a . Incr (m a) -> m (Incr a))
       -> Term (m b)
       -> n b
gfoldT var lam app ty pi dist = go
  where go :: Term (m x) -> n x
        go = \case
          Var a -> var a
          Lam (Scope b) -> lam (go (dist <$> b))
          f :$ a -> app (go f) (go a)
          Type -> ty
          Pi t (Scope b) -> pi (go t) (go (dist <$> b))

joinT :: Term (Term a) -> Term a
joinT = gfoldT id (Lam . Scope) (:$) Type (\ t -> Pi t . Scope) distT

distT :: Incr (Term a) -> Term (Incr a)
distT Z     = Var Z
distT (S t) = S <$> t


-- | Bind occurrences of a 'Name' in a 'Term' term, producing a 'Scope' in which the 'Name' is bound.
bind :: Eq a => a -> Term a -> Scope a
bind name = Scope . fmap (match name)

-- | Substitute a 'Term' term for the free variable in a given 'Scope', producing a closed 'Term' term.
instantiate :: Term a -> Scope a -> Term a
instantiate t (Scope b) = b >>= subst t . fmap Var


instance Applicative Term where
  pure = Var
  (<*>) = ap

instance Monad Term where
  a >>= f = joinT (f <$> a)


identityT :: Term Name
identityT = pi (Local (Root "x") ::: Type) (pi (Local (Root "y") ::: pure (Local (Root "x"))) (pure (Local (Root "x"))))

identity :: Term Name
identity = lam (Local (Root "x")) (lam (Local (Root "y")) (pure (Local (Root "y"))))

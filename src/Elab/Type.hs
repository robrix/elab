{-# LANGUAGE DeriveTraversable, LambdaCase, RankNTypes, ScopedTypeVariables, TypeOperators #-}
module Elab.Type where

import Control.Monad (ap)
import Data.Foldable (foldl', toList)
import Elab.Name
import Elab.Pretty
import Elab.Stack
import Prelude hiding (pi)

data Type a
  = Type
  | Lam          (Scope a)
  | Pi  (Type a) (Scope a)
  | a :$ Stack (Type a)
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Pretty a => Pretty (Type a) where
  prettys (h :$ Nil) = prettys h
  prettys (h :$ sp)  = prettys h . showChar ' ' . prettys (toList sp)
  prettys Type       = showString "Type"
  prettys (Lam b)    = showString "λ " . showParen True (prettys b)
  prettys (Pi t b)   = showString "π " . prettys t . showString " . " . prettys b

newtype Scope a = Scope (Type (Incr a))
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

instance Pretty a => Pretty (Scope a) where
  prettys (Scope a) = prettys a


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


gfoldT :: forall m n b
       .  (forall a . n (Incr a) -> n a)
       -> (forall a . m a -> Stack (n a) -> n a)
       -> (forall a . n a)
       -> (forall a . n a -> n (Incr a) -> n a)
       -> (forall a . Incr (m a) -> m (Incr a))
       -> Type (m b)
       -> n b
gfoldT lam app ty pi dist = go
  where go :: Type (m x) -> n x
        go = \case
          Lam (Scope b) -> lam (go (dist <$> b))
          f :$ a -> app f (fmap go a)
          Type -> ty
          Pi t (Scope b) -> pi (go t) (go (dist <$> b))

joinT :: Type (Type a) -> Type a
joinT = gfoldT (Lam . Scope) ($$*) Type (\ t -> Pi t . Scope) distT

distT :: Incr (Type a) -> Type (Incr a)
distT Z     = pure Z
distT (S t) = S <$> t

-- | Bind occurrences of a 'Name' in a 'Type' term, producing a 'Scope' in which the 'Name' is bound.
bind :: Eq a => a -> Type a -> Scope a
bind name = Scope . fmap (match name)

-- | Substitute a 'Type' term for the free variable in a given 'Scope', producing a closed 'Type' term.
instantiate :: Type a -> Scope a -> Type a
instantiate t (Scope b) = b >>= subst t . fmap pure


instance Applicative Type where
  pure a = a :$ Nil
  (<*>) = ap

instance Monad Type where
  a >>= f = joinT (f <$> a)

identityT :: Type Name
identityT = pi (Local (Root "x") ::: Type) (pi (Local (Root "y") ::: pure (Local (Root "x"))) (pure (Local (Root "x"))))

identity :: Type Name
identity = lam (Local (Root "x")) (lam (Local (Root "y")) (pure (Local (Root "y"))))

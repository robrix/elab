{-# LANGUAGE DeriveFunctor, FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Elab.Check where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader
import Control.Monad (unless)
import qualified Data.Map as Map
import Elab.Name
import Elab.Type (Type(..), Typing(..))
import qualified Elab.Type as Type
import Prelude hiding (fail)

type Context = [Type Name]
type Signature = Map.Map Name (Type Name)

newtype Check a = Check { runCheck :: ReaderC (Type Name) (ReaderC Signature (ReaderC Gensym (FreshC (FailC VoidC)))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

newtype Infer a = Infer { runInfer :: ReaderC Signature (ReaderC Gensym (FreshC (FailC VoidC))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

free :: Name -> Infer (Type Name)
free v = Infer $ do
  sig <- ask
  maybe (fail ("Variable not in scope: " <> show v)) pure (Map.lookup v sig)

lam :: Type Name -> (Name -> Check (Type Name)) -> Check (Type Name)
lam ty body = Check $ do
  x <- Gensym <$> gensym ""
  b' <- x ::: ty |- runCheck (body x)
  pure (Type.pi (x ::: ty) b')

type' :: Infer (Type Name)
type' = pure Type

($$) :: Infer (Type Name) -> Check (Type Name) -> Infer (Type Name)
f $$ a = do
  f' <- f
  case f' of
    Pi t b -> do
      a' <- ascribe t a
      pure (Type.instantiate a' b)
    _ -> fail ("expected function type, got " <> show f')

ascribe :: Type Name -> Check (Type Name) -> Infer (Type Name)
ascribe ty = Infer . runReader ty . runCheck

switch :: Infer (Type Name) -> Check (Type Name)
switch m = Check $ ReaderC $ \ expected -> do
  actual <- runInfer m
  unless (expected == actual) $
    fail ("expected: " <> show expected <> "\n  actual: " <> show actual)
  pure actual

goal :: Check (Type Name)
goal = Check ask


(|-) :: (Carrier sig m, Member (Reader Signature) sig) => Typing Name -> m a -> m a
a ::: ty |- m = local (Map.insert a ty) m

infix 5 |-

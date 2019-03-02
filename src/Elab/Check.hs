{-# LANGUAGE DeriveFunctor, FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Elab.Check where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader
import Control.Monad (unless)
import Control.Monad.Trans.Class
import qualified Data.Map as Map
import Elab.Name
import Elab.Term (Term(..), Typing(..))
import qualified Elab.Term as Term
import Prelude hiding (fail)

type Type = Term Name
type Context = [Type]
type Signature = Map.Map Name Type

newtype Check a = Check { runCheck :: ReaderC Type (ReaderC Signature (ReaderC Gensym (FreshC (FailC VoidC)))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

newtype Infer a = Infer { runInfer :: ReaderC Signature (ReaderC Gensym (FreshC (FailC VoidC))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

free :: Name -> Infer Type
free v = Infer $ do
  sig <- ask
  maybe (fail ("Variable not in scope: " <> show v)) pure (Map.lookup v sig)

lam :: Type -> (Name -> Check Type) -> Check Type
lam ty body = do
  x <- Gensym <$> Check (gensym "")
  Term.pi (x ::: ty) <$> body x

type' :: Infer Type
type' = pure Type

($$) :: Infer Type -> Check Type -> Infer Type
f $$ a = do
  f' <- f
  case f' of
    Pi t b -> do
      a' <- ascribe t a
      pure (Term.instantiate a' b)
    _ -> fail ("expected function type, got " <> show f')

ascribe :: Type -> Check Type -> Infer Type
ascribe ty = Infer . runReader ty . runCheck

switch :: Infer Type -> Check Type
switch m = Check $ do
  expected <- ask
  actual <- lift (runInfer m)
  unless (expected == actual) $
    fail ("expected: " <> show expected <> "\n  actual: " <> show actual)
  pure actual

(|-) :: (Carrier sig m, Member (Reader Signature) sig) => Typing Name -> m a -> m a
a ::: ty |- m = local (Map.insert a ty) m

infix 5 |-

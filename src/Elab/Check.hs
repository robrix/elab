{-# LANGUAGE DeriveFunctor, FlexibleContexts, GeneralizedNewtypeDeriving #-}
module Elab.Check where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Fresh
import Control.Effect.Reader
import Control.Monad (unless)
import qualified Data.Map as Map
import Elab.Name
import Elab.Type (Type(..), Typed(..))
import qualified Elab.Type as Type
import Prelude hiding (fail)

type Context = [Type Name]
type Signature = Map.Map Name (Type Name)
type Value = Type Name

newtype Check a = Check { runCheck :: ReaderC (Type Name) (ReaderC Signature (ReaderC Gensym (FreshC (FailC VoidC)))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

newtype Infer a = Infer { runInfer :: ReaderC Signature (ReaderC Gensym (FreshC (FailC VoidC))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

assumption :: Name -> Infer (Typed Value Name)
assumption v = Infer $ do
  sig <- ask
  maybe (fail ("Variable not in scope: " <> show v)) (pure . (pure v :::)) (Map.lookup v sig)

introduce :: (Name -> Check (Typed Value Name)) -> Check (Typed Value Name)
introduce body = do
  expected <- goal
  case expected of
    Pi t b -> Check $ do
      x <- Gensym <$> gensym "introduce"
      b' ::: bT <- x ::: t |- runCheck (goalIs (Type.instantiate (pure x) b) (body x))
      pure (Type.lam x b' ::: Type.pi (x ::: t) bT)
    _ -> fail ("expected function type, got " <> show expected)

type' :: Infer (Typed Value Name)
type' = pure (Type ::: Type)

pi :: Check (Typed Value Name) -> (Name -> Check (Typed Value Name)) -> Infer (Typed Value Name)
pi t body = do
  t' ::: _ <- ascribe Type t
  x <- Infer (Gensym <$> gensym "pi")
  body' ::: _ <- Infer (x ::: t' |- runInfer (ascribe Type (body x)))
  pure (Type.pi (x ::: t') body' ::: Type)

($$) :: Infer (Typed Value Name) -> Check (Typed Value Name) -> Infer (Typed Value Name)
f $$ a = do
  f' ::: fT <- f
  case fT of
    Pi t b -> do
      a' ::: aT <- ascribe t a
      pure (f' Type.$$ a' ::: Type.instantiate aT b)
    _ -> fail ("expected function type, got " <> show f')

ascribe :: Type Name -> Check a -> Infer a
ascribe ty = Infer . runReader ty . runCheck

switch :: Infer (Typed Value Name) -> Check (Typed Value Name)
switch m = do
  expected <- goal
  val ::: actual <- Check (ReaderC (const (runInfer m)))
  unless (expected == actual) $
    fail ("expected: " <> show expected <> "\n  actual: " <> show actual)
  pure (val ::: actual)

goal :: Check (Type Name)
goal = Check ask

goalIs :: Type Name -> Check a -> Check a
goalIs ty = Check . local (const ty) . runCheck


(|-) :: (Carrier sig m, Member (Reader Signature) sig) => Typed Name Name -> m a -> m a
a ::: ty |- m = local (Map.insert a ty) m

infix 5 |-


runInfer' :: Signature -> Infer a -> Either String a
runInfer' sig = run . runFail . runFresh . runReader (Root "root") . runReader sig  . runInfer

runCheck' :: Signature -> Type Name -> Check a -> Either String a
runCheck' sig ty = runInfer' sig . ascribe ty

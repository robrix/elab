{-# LANGUAGE DeriveTraversable, FlexibleContexts, GeneralizedNewtypeDeriving, TypeOperators #-}
module Elab.Elab where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Fresh
import Control.Effect.Reader
import Control.Effect.Writer
import Control.Monad (unless)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Elab.Name
import Elab.Type (Type(..))
import qualified Elab.Type as Type
import Prelude hiding (fail)

type Context = Map.Map Name (Type Name)
type Value = Type Name

newtype Check a = Check { runCheck :: ReaderC (Type Name) (ReaderC Context (ReaderC Gensym (FreshC (FailC VoidC)))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

newtype Infer a = Infer { runInfer :: ReaderC Context (ReaderC Gensym (FreshC (FailC VoidC))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

assume :: Name -> Infer (Value ::: Type Name)
assume v = (pure v :::) <$> Infer (lookupVar v)

intro :: (Name -> Check (Value ::: Type Name)) -> Check (Value ::: Type Name)
intro body = do
  expected <- goal
  case expected of
    Pi t b -> Check $ do
      x <- Gensym <$> gensym "intro"
      b' ::: bT <- x ::: t |- runCheck (goalIs (Type.instantiate (pure x) b) (body x))
      pure (Type.lam x b' ::: Type.pi (x ::: t) bT)
    _ -> fail ("expected function type, got " <> show expected)

type' :: Infer (Value ::: Type Name)
type' = pure (Type ::: Type)

pi :: Check (Value ::: Type Name) -> (Name -> Check (Value ::: Type Name)) -> Infer (Value ::: Type Name)
pi t body = do
  t' ::: _ <- ascribe Type t
  x <- Infer (Gensym <$> gensym "pi")
  body' ::: _ <- Infer (x ::: t' |- runInfer (ascribe Type (body x)))
  pure (Type.pi (x ::: t') body' ::: Type)

($$) :: Infer (Value ::: Type Name) -> Check (Value ::: Type Name) -> Infer (Value ::: Type Name)
f $$ a = do
  f' ::: fT <- f
  case fT of
    Pi t b -> do
      a' ::: aT <- ascribe t a
      pure (f' Type.$$ a' ::: Type.instantiate aT b)
    _ -> fail ("expected function type, got " <> show f')

ascribe :: Type Name -> Check a -> Infer a
ascribe ty = Infer . runReader ty . runCheck

switch :: Infer (Value ::: Type Name) -> Check (Value ::: Type Name)
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


(|-) :: (Carrier sig m, Member (Reader Context) sig) => Name ::: Type Name -> m a -> m a
a ::: ty |- m = local (Map.insert a ty) m

infix 5 |-

lookupVar :: (Carrier sig m, Member (Reader Context) sig, MonadFail m) => Name -> m (Type Name)
lookupVar v = asks (Map.lookup v) >>= maybe (fail ("Variable not in scope: " <> show v)) pure


runInfer' :: Context -> Infer a -> Either String a
runInfer' sig = run . runFail . runFresh . runReader (Root "root") . runReader sig  . runInfer

runCheck' :: Context -> Type Name -> Check a -> Either String a
runCheck' sig ty = runInfer' sig . ascribe ty


newtype Elab a = Elab { runElab :: ReaderC (Type Name) (ReaderC Context (ReaderC Gensym (FreshC (WriterC (Set.Set (Contextual (Equation (Value ::: Type Name)))) (FailC VoidC))))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

assume' :: Name -> Elab (Value ::: Type Name)
assume' v = Elab $ do
  a ::: ty <- ask >>= exists
  _A <- lookupVar v
  ctx <- ask
  tell (Set.singleton (ctx :|- pure v ::: _A :===: a ::: ty))
  pure (a ::: ty)


exists :: (Carrier sig m, Member Fresh sig, Member (Reader Context) sig, Member (Reader Gensym) sig) => Type Name -> m (Value ::: Type Name)
exists ty = do
  ctx <- ask
  -- FIXME: add meta names
  n <- Gensym <$> gensym "_meta_"
  pure (pure n Type.$$* fmap pure (Map.keys (ctx :: Context)) ::: ty)


data Equation a
  = a :===: a
  deriving (Eq, Ord, Show)

infix 3 :===:

data Contextual a = Context :|- a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 1 :|-

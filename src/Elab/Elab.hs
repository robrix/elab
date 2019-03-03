{-# LANGUAGE DeriveTraversable, FlexibleContexts, GeneralizedNewtypeDeriving, TypeOperators #-}
module Elab.Elab where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Local)
import Control.Effect.Writer
import Control.Monad (unless)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Elab.Name
import Elab.Type (Type(..))
import qualified Elab.Type as Type
import Prelude hiding (fail)

type Context = Map.Map Name
type Value = Type

newtype Check a = Check { runCheck :: ReaderC (Type Name) (ReaderC (Context (Type Name)) (ReaderC Gensym (FreshC (FailC VoidC)))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

newtype Infer a = Infer { runInfer :: ReaderC (Context (Type Name)) (ReaderC Gensym (FreshC (FailC VoidC))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

assume :: Name -> Infer (Value Name ::: Type Name)
assume v = (pure v :::) <$> Infer (lookupVar v)

intro :: (Name -> Check (Value Name ::: Type Name)) -> Check (Value Name ::: Type Name)
intro body = do
  expected <- goal
  case expected of
    Pi t b -> Check $ do
      x <- Local <$> gensym "intro"
      b' ::: bT <- x ::: t |- runCheck (goalIs (Type.instantiate (pure x) b) (body x))
      pure (Type.lam x b' ::: Type.pi (x ::: t) bT)
    _ -> fail ("expected function type, got " <> show expected)

type' :: Infer (Value Name ::: Type Name)
type' = pure (Type ::: Type)

pi :: Check (Value Name ::: Type Name) -> (Name -> Check (Value Name ::: Type Name)) -> Infer (Value Name ::: Type Name)
pi t body = do
  t' ::: _ <- ascribe Type t
  x <- Infer (Local <$> gensym "pi")
  body' ::: _ <- Infer (x ::: t' |- runInfer (ascribe Type (body x)))
  pure (Type.pi (x ::: t') body' ::: Type)

($$) :: Infer (Value Name ::: Type Name) -> Check (Value Name ::: Type Name) -> Infer (Value Name ::: Type Name)
f $$ a = do
  f' ::: fT <- f
  case fT of
    Pi t b -> do
      a' ::: aT <- ascribe t a
      pure (f' Type.$$ a' ::: Type.instantiate aT b)
    _ -> fail ("expected function type, got " <> show f')

ascribe :: Type Name -> Check a -> Infer a
ascribe ty = Infer . runReader ty . runCheck

switch :: Infer (Value Name ::: Type Name) -> Check (Value Name ::: Type Name)
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


(|-) :: (Carrier sig m, Member (Reader (Context (Type Name))) sig) => Name ::: Type Name -> m a -> m a
a ::: ty |- m = local (Map.insert a ty) m

infix 5 |-

lookupVar :: (Carrier sig m, Member (Reader (Context ty)) sig, MonadFail m) => Name -> m ty
lookupVar v = asks (Map.lookup v) >>= maybe (fail ("Variable not in scope: " <> show v)) pure


runInfer' :: Context (Type Name) -> Infer a -> Either String a
runInfer' sig = run . runFail . runFresh . runReader (Root "root") . runReader sig  . runInfer

runCheck' :: Context (Type Name) -> Type Name -> Check a -> Either String a
runCheck' sig ty = runInfer' sig . ascribe ty


newtype Elab a = Elab { runElab :: ReaderC (Type Meta) (ReaderC (Context (Type Meta)) (ReaderC Gensym (FreshC (WriterC (Set.Set (Contextual (Equation (Value Meta ::: Type Meta)))) (FailC VoidC))))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

assume' :: Name -> Elab (Value Meta ::: Type Meta)
assume' v = do
  res <- goal' >>= exists
  _A <- Elab (lookupVar v)
  unify (pure (Name v) ::: _A :===: res)
  pure res

intro' :: (Name -> Elab (Value Meta ::: Type Meta)) -> Elab (Value Meta ::: Type Meta)
intro' body = do
  res <- goal' >>= exists
  _A ::: _ <- exists Type
  x <- freshName "intro"
  _B ::: _ <- x ::: _A ||- exists Type
  u ::: _ <- x ::: _A ||- goalIs' _B (body x)
  unify (Type.lam (Name x) u ::: Type.pi (Name x ::: _A) _B :===: res)
  pure res

type'' :: Elab (Value Meta ::: Type Meta)
type'' = do
  res <- goal' >>= exists
  unify (Type ::: Type :===: res)
  pure res

pi' :: Elab (Value Meta ::: Type Meta) -> (Name -> Elab (Value Meta ::: Type Meta)) -> Elab (Value Meta ::: Type Meta)
pi' t body = do
  res <- goal' >>= exists
  t' ::: _ <- goalIs' Type t
  x <- freshName "pi"
  b' ::: _ <- x ::: t' ||- goalIs' Type (body x)
  unify (Type.pi (Name x ::: t') b' ::: Type :===: res)
  pure res

($$$) :: Elab (Value Meta ::: Type Meta) -> Elab (Value Meta ::: Type Meta) -> Elab (Value Meta ::: Type Meta)
f $$$ a = do
  res <- goal' >>= exists
  _A ::: _ <- exists Type
  _B ::: _ <- exists Type
  x <- freshName "$$"
  f' ::: _ <- goalIs' (Type.pi (Name x ::: _A) _B) f
  a' ::: _ <- goalIs' _A a
  unify (f' Type.$$ a' ::: _B :===: res)
  pure res


freshName :: String -> Elab Name
freshName s = Local <$> Elab (gensym s)

context :: Elab (Context (Type Meta))
context = Elab ask

exists :: Type Meta -> Elab (Value Meta ::: Type Meta)
exists ty = do
  ctx <- context
  -- FIXME: add meta names
  n <- Elab (Meta <$> gensym "meta")
  pure (pure n Type.$$* map (pure . Name) (Map.keys (ctx :: Context (Type Meta))) ::: ty)

goal' :: Elab (Type Meta)
goal' = Elab ask

goalIs' :: Type Meta -> Elab a -> Elab a
goalIs' ty = Elab . local (const ty) . runElab

(||-) :: Name ::: Type Meta -> Elab a -> Elab a
a ::: ty ||- m = Elab (local (Map.insert a ty) (runElab m))

infix 5 ||-

unify :: Equation (Value Meta ::: Type Meta) -> Elab ()
unify constraint = context >>= Elab . tell . Set.singleton . (:|- constraint)


data Equation a
  = a :===: a
  deriving (Eq, Ord, Show)

infix 3 :===:

data Contextual a = Context (Type Meta) :|- a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 1 :|-

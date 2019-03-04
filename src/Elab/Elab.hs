{-# LANGUAGE DeriveTraversable, FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase, TypeOperators #-}
module Elab.Elab where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Control.Effect.Writer
import Control.Monad (join, unless, when)
import Data.Foldable (fold, foldl')
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Elab.Name
import Elab.Stack
import Elab.Type (Type(..))
import qualified Elab.Type as Type
import Prelude hiding (fail)

type Context = Map.Map Name
type Value = Type

newtype Check a = Check { unCheck :: ReaderC (Type Name) (ReaderC (Context (Type Name)) (ReaderC Gensym (FreshC (FailC VoidC)))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

newtype Infer a = Infer { unInfer :: ReaderC (Context (Type Name)) (ReaderC Gensym (FreshC (FailC VoidC))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

assume :: Name -> Infer (Value Name ::: Type Name)
assume v = (pure v :::) <$> Infer (lookupVar v)

intro :: (Name -> Check (Value Name ::: Type Name)) -> Check (Value Name ::: Type Name)
intro body = do
  expected <- goal
  case expected of
    Pi t b -> Check $ do
      x <- Local <$> gensym "intro"
      b' ::: bT <- x ::: t |- unCheck (goalIs (Type.instantiate (pure x) b) (body x))
      pure (Type.lam x b' ::: Type.pi (x ::: t) bT)
    _ -> fail ("expected function type, got " <> show expected)

type' :: Infer (Value Name ::: Type Name)
type' = pure (Type ::: Type)

pi :: Check (Value Name ::: Type Name) -> (Name -> Check (Value Name ::: Type Name)) -> Infer (Value Name ::: Type Name)
pi t body = do
  t' ::: _ <- ascribe Type t
  x <- Infer (Local <$> gensym "pi")
  body' ::: _ <- Infer (x ::: t' |- unInfer (ascribe Type (body x)))
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
ascribe ty = Infer . runReader ty . unCheck

switch :: Infer (Value Name ::: Type Name) -> Check (Value Name ::: Type Name)
switch m = do
  expected <- goal
  val ::: actual <- Check (ReaderC (const (unInfer m)))
  unless (expected == actual) $
    fail ("expected: " <> show expected <> "\n  actual: " <> show actual)
  pure (val ::: actual)

goal :: Check (Type Name)
goal = Check ask

goalIs :: Type Name -> Check a -> Check a
goalIs ty = Check . local (const ty) . unCheck


(|-) :: (Carrier sig m, Member (Reader (Context (Type Name))) sig) => Name ::: Type Name -> m a -> m a
a ::: ty |- m = local (Map.insert a ty) m

infix 5 |-

lookupVar :: (Carrier sig m, Member (Reader (Context ty)) sig, MonadFail m) => Name -> m ty
lookupVar v = asks (Map.lookup v) >>= maybe (fail ("Variable not in scope: " <> show v)) pure


runInfer :: Infer a -> Either String a
runInfer = run . runFail . runFresh . runReader (Root "root") . runReader mempty  . unInfer

runCheck :: Type Name -> Check a -> Either String a
runCheck ty = runInfer . ascribe ty


newtype Elab a = Elab { unElab :: ReaderC (Type Meta) (ReaderC (Context (Type Meta)) (WriterC (Set.Set Constraint) (ReaderC Gensym (FreshC (FailC VoidC))))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

assume' :: Name -> Elab (Value Meta ::: Type Meta)
assume' v = do
  res <- goal' >>= exists
  _A <- Elab (lookupVar v)
  res <$ unify (pure (Name v) ::: _A :===: res)

intro' :: (Name -> Elab (Value Meta ::: Type Meta)) -> Elab (Value Meta ::: Type Meta)
intro' body = do
  res <- goal' >>= exists
  _A ::: _ <- exists Type
  x <- freshName "intro"
  _B ::: _ <- x ::: _A ||- exists Type
  u ::: _ <- x ::: _A ||- goalIs' _B (body x)
  res <$ unify (Type.lam (Name x) u ::: Type.pi (Name x ::: _A) _B :===: res)

type'' :: Elab (Value Meta ::: Type Meta)
type'' = do
  res <- goal' >>= exists
  res <$ unify (Type ::: Type :===: res)

pi' :: Elab (Value Meta ::: Type Meta) -> (Name -> Elab (Value Meta ::: Type Meta)) -> Elab (Value Meta ::: Type Meta)
pi' t body = do
  res <- goal' >>= exists
  t' ::: _ <- goalIs' Type t
  x <- freshName "pi"
  b' ::: _ <- x ::: t' ||- goalIs' Type (body x)
  res <$ unify (Type.pi (Name x ::: t') b' ::: Type :===: res)

($$$) :: Elab (Value Meta ::: Type Meta) -> Elab (Value Meta ::: Type Meta) -> Elab (Value Meta ::: Type Meta)
f $$$ a = do
  res <- goal' >>= exists
  _A ::: _ <- exists Type
  _B ::: _ <- exists Type
  x <- freshName "$$"
  f' ::: _ <- goalIs' (Type.pi (Name x ::: _A) _B) f
  a' ::: _ <- goalIs' _A a
  res <$ unify (f' Type.$$ a' ::: _B :===: res)


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
goalIs' ty (Elab m) = Elab (local (const ty) m)

(||-) :: Name ::: Type Meta -> Elab a -> Elab a
a ::: ty ||- Elab m = Elab (local (Map.insert a ty) m)

infix 5 ||-

unify :: Equation (Value Meta ::: Type Meta) -> Elab ()
unify constraint = context >>= Elab . tell . Set.singleton . (:|-: constraint)


data Equation a
  = a :===: a
  deriving (Eq, Ord, Show)

infix 3 :===:

data Contextual a = Context (Type Meta) :|-: a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 1 :|-:

type Constraint = Contextual (Equation (Value Meta ::: Type Meta))
type Blocked = Map.Map Gensym (Set.Set Constraint)
type Substitution = Map.Map Gensym (Value Meta)
type Queue = Seq.Seq Constraint

data Solution
  = Gensym := Value Meta
  deriving (Eq, Ord, Show)

infix 5 :=

runElab :: Maybe (Type Meta) -> Elab (Value Meta ::: Type Meta) -> Either String (Value Name ::: Type Name)
runElab ty m = run . runFail . runFresh . runReader (Root "elab") $ do
  ty' <- maybe (pure . Meta <$> gensym "meta") pure ty
  (constraints, val ::: ty) <- runWriter . runReader (mempty :: Context (Type Meta)) . runReader ty' . unElab $ do
    val <- exists ty'
    m' <- m
    m' <$ unify (m' :===: val)
  subst <- solver constraints
  val' <- substTy subst val
  ty' <- substTy subst ty
  pure (val' ::: ty')

solver :: (Carrier sig m, Effect sig, Member Fresh sig, Member (Reader Gensym) sig, MonadFail m) => Set.Set Constraint -> m Substitution
solver constraints = execState Map.empty . evalState (Seq.empty :: Queue) $ do
  stuck <- fmap fold . execState (Map.empty :: Blocked) $ do
    enqueueAll constraints
    step
  unless (null stuck) $ fail ("stuck constraints: " ++ show stuck)

step :: (Carrier sig m, Effect sig, Member Fresh sig, Member (Reader Gensym) sig, Member (State Blocked) sig, Member (State Queue) sig, Member (State Substitution) sig, MonadFail m) => m ()
step = dequeue >>= \case
  Just c@(_ :|-: tm1 ::: ty1 :===: tm2 ::: ty2) -> do
    _S <- get
    case c of
      _ | s <- Map.restrictKeys _S (metaNames (fvs c)), not (null s) -> simplify (applyConstraint s c) >>= enqueueAll
        | Just (m, sp) <- pattern ty1 -> solve (m := Type.lams sp ty2)
        | Just (m, sp) <- pattern ty2 -> solve (m := Type.lams sp ty1)
        | Just (m, sp) <- pattern tm1 -> solve (m := Type.lams sp tm2)
        | Just (m, sp) <- pattern tm2 -> solve (m := Type.lams sp tm1)
        | otherwise -> block c
    step
  Nothing -> pure ()

block :: (Carrier sig m, Member (State Blocked) sig, MonadFail m) => Constraint -> m ()
block c = do
  let s = Set.singleton c
      mvars = metaNames (fvs c)
  when (null mvars) $ fail ("cannot block constraint without metavars: " ++ show c)
  modify (Map.unionWith (<>) (foldl' (\ m i -> Map.insertWith (<>) i s m) mempty mvars))

enqueueAll :: (Carrier sig m, Member (State Queue) sig, Foldable t) => t Constraint -> m ()
enqueueAll = modify . flip (foldl' (Seq.|>))

dequeue :: (Carrier sig m, Member (State Queue) sig) => m (Maybe Constraint)
dequeue = gets Seq.viewl >>= \case
  Seq.EmptyL -> pure Nothing
  h Seq.:< q -> Just h <$ put q

pattern :: Type Meta -> Maybe (Gensym, Stack Meta)
pattern (Free (Meta m) :$ sp) = (,) m <$> traverse free sp
pattern _                     = Nothing

free :: Type a -> Maybe a
free (Free v :$ Nil) = Just v
free _               = Nothing

solve :: (Carrier sig m, Member (State Blocked) sig, Member (State Queue) sig, Member (State Substitution) sig) => Solution -> m ()
solve (m := v) = do
  modify (Map.insert m v)
  cs <- gets (fromMaybe Set.empty . Map.lookup m)
  enqueueAll cs
  modify (Map.delete m :: Blocked -> Blocked)

applyConstraint :: Substitution -> Constraint -> Constraint
applyConstraint subst (ctx :|-: tm1 ::: ty1 :===: tm2 ::: ty2) = applyContext subst ctx :|-: applyType subst tm1 ::: applyType subst ty1 :===: applyType subst tm2 ::: applyType subst ty2

applyContext :: Substitution -> Context (Type Meta) -> Context (Type Meta)
applyContext = fmap . applyType

applyType :: Substitution -> Type Meta -> Type Meta
applyType subst ty = ty >>= \case
  Name n -> pure (Name n)
  Meta m -> fromMaybe (pure (Meta m)) (Map.lookup m subst)

substTy :: (Carrier sig m, MonadFail m) => Map.Map Gensym (Type Meta) -> Type Meta -> m (Type Name)
substTy subst = fmap (fmap join) . traverse $ \case
  Name n -> pure (pure n)
  Meta m -> maybe (fail ("unsolved metavariable " ++ show m)) (substTy subst) (Map.lookup m subst)

fvs :: Constraint -> Set.Set Meta
fvs (ctx :|-: tm1 ::: ty1 :===: tm2 ::: ty2) = foldMap go ctx <> go tm1 <> go ty1 <> go tm2 <> go ty2
  where go = foldMap Set.singleton

metaNames :: Set.Set Meta -> Set.Set Gensym
metaNames = foldMap $ \case
  Meta m -> Set.singleton m
  _      -> Set.empty

simplify :: ( Carrier sig m
            , Effect sig
            , Member Fresh sig
            , Member (Reader Gensym) sig
            , MonadFail m
            )
         => Constraint
         -> m (Set.Set Constraint)
simplify (ctx :|-: c) = execWriter (go c)
  where go = \case
          tm1 ::: ty1 :===: tm2 ::: ty2 | tm1 == tm2, ty1 == ty2 -> pure ()
          Pi t1 b1 ::: Type :===: Pi t2 b2 ::: Type -> do
            go (t1 ::: Type :===: t2 ::: Type)
            n <- Name . Local <$> gensym "simplify"
            go (Type.instantiate (pure n) b1 ::: Type :===: Type.instantiate (pure n) b2 ::: Type)
          c@(t1 :===: t2)
            | stuck t1 || stuck t2 -> tell (Set.singleton (ctx :|-: c))
            | otherwise            -> fail ("unsimplifiable constraint: " ++ show c)

        stuck (v ::: ty) = stuckType v || stuckType ty
        stuckType (Free (Meta _) :$ _) = True
        stuckType _                    = False

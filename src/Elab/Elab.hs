{-# LANGUAGE DeriveTraversable, FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase, TypeOperators #-}
module Elab.Elab where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Control.Effect.Writer
import Control.Monad ((>=>), join, unless, when)
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

newtype Elab a = Elab { unElab :: ReaderC (Type Meta) (ReaderC (Context (Type Meta)) (WriterC (Set.Set HetConstraint) (ReaderC Gensym (FreshC (FailC VoidC))))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

assume :: Name -> Elab (Value Meta ::: Type Meta)
assume v = do
  res <- goal >>= exists
  _A <- Elab (lookupVar v)
  res <$ unify (pure (Name v) ::: _A :===: res)

intro :: (Name -> Elab (Value Meta ::: Type Meta)) -> Elab (Value Meta ::: Type Meta)
intro body = do
  res <- goal >>= exists
  _A ::: _ <- exists Type
  x <- freshName "intro"
  _B ::: _ <- x ::: _A |- exists Type
  u ::: _ <- x ::: _A |- goalIs _B (body x)
  res <$ unify (Type.lam (Name x) u ::: Type.pi (Name x ::: _A) _B :===: res)

type' :: Elab (Value Meta ::: Type Meta)
type' = do
  res <- goal >>= exists
  res <$ unify (Type ::: Type :===: res)

pi :: Elab (Value Meta ::: Type Meta) -> (Name -> Elab (Value Meta ::: Type Meta)) -> Elab (Value Meta ::: Type Meta)
pi t body = do
  res <- goal >>= exists
  t' ::: _ <- goalIs Type t
  x <- freshName "pi"
  b' ::: _ <- x ::: t' |- goalIs Type (body x)
  res <$ unify (Type.pi (Name x ::: t') b' ::: Type :===: res)

($$) :: Elab (Value Meta ::: Type Meta) -> Elab (Value Meta ::: Type Meta) -> Elab (Value Meta ::: Type Meta)
f $$ a = do
  res <- goal >>= exists
  _A ::: _ <- exists Type
  _B ::: _ <- exists Type
  x <- freshName "$$"
  f' ::: _ <- goalIs (Type.pi (Name x ::: _A) _B) f
  a' ::: _ <- goalIs _A a
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

goal :: Elab (Type Meta)
goal = Elab ask

goalIs :: Type Meta -> Elab a -> Elab a
goalIs ty (Elab m) = Elab (local (const ty) m)

(|-) :: Name ::: Type Meta -> Elab a -> Elab a
a ::: ty |- Elab m = Elab (local (Map.insert a ty) m)

infix 5 |-

unify :: Equation (Value Meta ::: Type Meta) -> Elab ()
unify constraint = context >>= Elab . tell . Set.singleton . (:|-: constraint)

lookupVar :: (Carrier sig m, Member (Reader (Context ty)) sig, MonadFail m) => Name -> m ty
lookupVar v = asks (Map.lookup v) >>= maybe (fail ("Variable not in scope: " <> show v)) pure


data Equation a
  = a :===: a
  deriving (Eq, Ord, Show)

infix 3 :===:

data Contextual a = Context (Type Meta) :|-: a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 1 :|-:

type HetConstraint = Contextual (Equation (Value Meta ::: Type Meta))
type Blocked = Map.Map Gensym (Set.Set HetConstraint)
type Substitution = Map.Map Gensym (Value Meta)
type Queue = Seq.Seq HetConstraint

data Solution
  = Gensym := Value Meta
  deriving (Eq, Ord, Show)

infix 5 :=

runElab :: Maybe (Type Meta) -> Elab (Value Meta ::: Type Meta) -> Either String (Value Name ::: Type Name)
runElab ty m = run . runFail . runFresh . runReader (Root "elab") $ do
  ty' <- maybe (pure . Meta <$> gensym "meta") pure ty
  (constraints, res) <- runWriter . runReader mempty . runReader ty' . unElab $ do
    val <- exists ty'
    m' <- m
    m' <$ unify (m' :===: val)
  subst <- solver constraints
  substTyped subst res

solver :: (Carrier sig m, Effect sig, Member Fresh sig, Member (Reader Gensym) sig, MonadFail m) => Set.Set HetConstraint -> m Substitution
solver constraints = execState Map.empty $ do
  queue <- execState (Seq.empty :: Queue) $ do
    stuck <- fmap fold . execState (Map.empty :: Blocked) $ do
      enqueueAll constraints
      step
    unless (null stuck) $ fail ("stuck constraints: " ++ show stuck)
  unless (null queue) $ fail ("stalled constraints: " ++ show queue)

step :: (Carrier sig m, Effect sig, Member Fresh sig, Member (Reader Gensym) sig, Member (State Blocked) sig, Member (State Queue) sig, Member (State Substitution) sig, MonadFail m) => m ()
step = do
  _S <- get
  dequeue >>= maybe (pure ()) (process _S >=> const step)

process :: (Carrier sig m, Effect sig, Member Fresh sig, Member (Reader Gensym) sig, Member (State Blocked) sig, Member (State Queue) sig, Member (State Substitution) sig, MonadFail m) => Substitution -> HetConstraint -> m ()
process _S c@(_ :|-: tm1 ::: ty1 :===: tm2 ::: ty2)
  | s <- Map.restrictKeys _S (metaNames (fvs c)), not (null s) = simplify (applyConstraint s c) >>= enqueueAll
  | Just (m, sp) <- pattern ty1 = solve (m := Type.lams sp ty2) >> get >>= \ _S -> process _S c
  | Just (m, sp) <- pattern ty2 = solve (m := Type.lams sp ty1) >> get >>= \ _S -> process _S c
  | Just (m, sp) <- pattern tm1 = solve (m := Type.lams sp tm2) >> get >>= \ _S -> process _S c
  | Just (m, sp) <- pattern tm2 = solve (m := Type.lams sp tm1) >> get >>= \ _S -> process _S c
  | otherwise = block c

block :: (Carrier sig m, Member (State Blocked) sig, MonadFail m) => HetConstraint -> m ()
block c = do
  let s = Set.singleton c
      mvars = metaNames (fvs c)
  when (null mvars) $ fail ("cannot block constraint without metavars: " ++ show c)
  modify (Map.unionWith (<>) (foldl' (\ m i -> Map.insertWith (<>) i s m) mempty mvars))

enqueueAll :: (Carrier sig m, Member (State Queue) sig, Foldable t) => t HetConstraint -> m ()
enqueueAll = modify . flip (foldl' (Seq.|>))

dequeue :: (Carrier sig m, Member (State Queue) sig) => m (Maybe HetConstraint)
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

applyConstraint :: Substitution -> HetConstraint -> HetConstraint
applyConstraint subst (ctx :|-: tm1 ::: ty1 :===: tm2 ::: ty2) = applyContext subst ctx :|-: applyType subst tm1 ::: applyType subst ty1 :===: applyType subst tm2 ::: applyType subst ty2

applyContext :: Substitution -> Context (Type Meta) -> Context (Type Meta)
applyContext = fmap . applyType

applyType :: Substitution -> Type Meta -> Type Meta
applyType subst ty = ty >>= \case
  Name n -> pure (Name n)
  Meta m -> fromMaybe (pure (Meta m)) (Map.lookup m subst)

substTyped :: (Carrier sig m, MonadFail m) => Map.Map Gensym (Type Meta) -> Value Meta ::: Type Meta -> m (Value Name ::: Type Name)
substTyped subst (val ::: ty) = (:::) <$> substTy subst val <*> substTy subst ty

substTy :: (Carrier sig m, MonadFail m) => Map.Map Gensym (Type Meta) -> Type Meta -> m (Type Name)
substTy subst = fmap (fmap join) . traverse $ \case
  Name n -> pure (pure n)
  Meta m -> maybe (fail ("unsolved metavariable " ++ show m)) (substTy subst) (Map.lookup m subst)

fvs :: HetConstraint -> Set.Set Meta
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
         => HetConstraint
         -> m (Set.Set HetConstraint)
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

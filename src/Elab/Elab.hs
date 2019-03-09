{-# LANGUAGE DeriveTraversable, FlexibleContexts, GeneralizedNewtypeDeriving, LambdaCase, TypeOperators #-}
module Elab.Elab where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Fresh
import Control.Effect.Reader hiding (Local)
import Control.Effect.State
import Control.Effect.Writer
import Control.Monad ((>=>), guard, join, unless, when)
import Data.Foldable (fold, foldl')
import qualified Data.Map as Map
import Data.Maybe (fromMaybe)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import Elab.Name
import Elab.Pretty
import Elab.Stack
import Elab.Type (Type(..))
import qualified Elab.Type as Type
import Prelude hiding (fail)
import Text.Show

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


expect :: Value Meta ::: Type Meta -> Elab (Value Meta ::: Type Meta)
expect exp = do
  res <- goal >>= exists
  res <$ unify (exp :===: res)

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
lookupVar v = asks (Map.lookup v) >>= maybe (fail ("Variable not in scope: " <> pretty v)) pure


data Equation a
  = a :===: a
  deriving (Eq, Ord, Show)

infix 3 :===:

instance Pretty a => Pretty (Equation a) where
  prettys (a1 :===: a2) = prettys a1 . showString " ≡ " . prettys a2


data Contextual a = Context (Type Meta) :|-: a
  deriving (Eq, Foldable, Functor, Ord, Show, Traversable)

infixr 1 :|-:

instance Pretty a => Pretty (Contextual a) where
  prettys (ctx :|-: a) = showString "Γ " . showListWith prettyBinding (Map.toList ctx) . showString " ⊢ " . prettys a
    where prettyBinding (v, t) = prettys v . showString " : " . prettys t


type HetConstraint = Contextual (Equation (Value Meta ::: Type Meta))
type HomConstraint = Contextual (Equation (Value Meta) ::: Type Meta)
type Blocked = Map.Map Gensym (Set.Set HomConstraint)
type Substitution = Map.Map Gensym (Value Meta)
type Queue = Seq.Seq HomConstraint

data Solution
  = Gensym := Value Meta
  deriving (Eq, Ord, Show)

infix 5 :=

instance Pretty Solution where
  prettys (n := v) = prettys n . showString " := " . prettys v


runElab :: Maybe (Type Meta) -> Elab (Value Meta ::: Type Meta) -> Either String (Value Name ::: Type Name)
runElab ty m = run . runFail . runFresh . runReader (Root "elab") $ do
  ty' <- maybe (pure . Meta <$> gensym "meta") pure ty
  (constraints, res) <- runWriter . runReader mempty . runReader ty' . unElab $ do
    val <- exists ty'
    m' <- m
    m' <$ unify (m' :===: val)
  subst <- solver (foldMap hetToHom constraints)
  substTyped subst res

solver :: (Carrier sig m, Effect sig, Member Fresh sig, Member (Reader Gensym) sig, MonadFail m) => Set.Set HomConstraint -> m Substitution
solver constraints = execState Map.empty $ do
  queue <- execState (Seq.empty :: Queue) $ do
    stuck <- fmap fold . execState (Map.empty :: Blocked) $ do
      enqueueAll constraints
      step
    unless (null stuck) $ fail ("stuck constraints: " ++ pretty stuck)
  unless (null queue) $ fail ("stalled constraints: " ++ pretty queue)

step :: (Carrier sig m, Effect sig, Member Fresh sig, Member (Reader Gensym) sig, Member (State Blocked) sig, Member (State Queue) sig, Member (State Substitution) sig, MonadFail m) => m ()
step = do
  _S <- get
  dequeue >>= maybe (pure ()) (process _S >=> const step)

process :: (Carrier sig m, Effect sig, Member Fresh sig, Member (Reader Gensym) sig, Member (State Blocked) sig, Member (State Queue) sig, Member (State Substitution) sig, MonadFail m) => Substitution -> HomConstraint -> m ()
process _S c@(_ :|-: (tm1 :===: tm2) ::: _)
  | tm1 == tm2 = pure ()
  | s <- Map.restrictKeys _S (metaNames (fvs c)), not (null s) = simplify (applyConstraint s c) >>= enqueueAll
  | Just (m, sp) <- pattern tm1 = solve (m := Type.lams sp tm2)
  | Just (m, sp) <- pattern tm2 = solve (m := Type.lams sp tm1)
  | otherwise = block c

block :: (Carrier sig m, Member (State Blocked) sig, MonadFail m) => HomConstraint -> m ()
block c = do
  let s = Set.singleton c
      mvars = metaNames (fvs c)
  when (null mvars) $ fail ("cannot block constraint without metavars: " ++ pretty c)
  modify (Map.unionWith (<>) (foldl' (\ m i -> Map.insertWith (<>) i s m) mempty mvars))

enqueueAll :: (Carrier sig m, Member (State Queue) sig, Foldable t) => t HomConstraint -> m ()
enqueueAll = modify . flip (foldl' (Seq.|>))

dequeue :: (Carrier sig m, Member (State Queue) sig) => m (Maybe HomConstraint)
dequeue = gets Seq.viewl >>= \case
  Seq.EmptyL -> pure Nothing
  h Seq.:< q -> Just h <$ put q

pattern :: Type Meta -> Maybe (Gensym, Stack Meta)
pattern (Free (Meta m) :$ sp) = (,) m <$> (traverse free sp >>= distinct)
pattern _                     = Nothing

free :: Type a -> Maybe a
free (Free v :$ Nil) = Just v
free _               = Nothing

distinct :: (Foldable t, Ord a) => t a -> Maybe (t a)
distinct sp = sp <$ guard (length (foldMap Set.singleton sp) == length sp)

solve :: (Carrier sig m, Member (State Blocked) sig, Member (State Queue) sig, Member (State Substitution) sig) => Solution -> m ()
solve (m := v) = do
  modify (Map.insert m v . fmap (applyType (Map.singleton m v)))
  cs <- gets (fromMaybe Set.empty . Map.lookup m)
  enqueueAll cs
  modify (Map.delete m :: Blocked -> Blocked)

applyConstraint :: Substitution -> HomConstraint -> HomConstraint
applyConstraint subst (ctx :|-: (tm1 :===: tm2) ::: ty) = applyContext subst ctx :|-: (applyType subst tm1 :===: applyType subst tm2) ::: applyType subst ty

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
  Meta m -> maybe (fail ("unsolved metavariable " ++ pretty m)) (substTy subst) (Map.lookup m subst)

fvs :: HomConstraint -> Set.Set Meta
fvs (ctx :|-: (tm1 :===: tm2) ::: ty) = foldMap go ctx <> go tm1 <> go tm2 <> go ty
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
         => HomConstraint
         -> m (Set.Set HomConstraint)
simplify = execWriter . go
  where go = \case
          _ :|-: (tm1 :===: tm2) ::: _ | tm1 == tm2 -> pure ()
          ctx :|-: (Pi t1 b1 :===: Pi t2 b2) ::: Type -> do
            go (ctx :|-: (t1 :===: t2) ::: Type)
            n <- Local <$> gensym "simplify"
            -- FIXME: this should insert some sort of dependency
            go (Map.insert n t1 ctx :|-: (Type.instantiate (pure (Name n)) b1 :===: Type.instantiate (pure (Name n)) b2) ::: Type)
          ctx :|-: (Lam f1 :===: Lam f2) ::: Pi t b -> do
            n <- Local <$> gensym "simplify"
            go (Map.insert n t ctx :|-: (Type.instantiate (pure (Name n)) f1 :===: Type.instantiate (pure (Name n)) f2) ::: Type.instantiate (pure (Name n)) b)
          c@(_ :|-: (t1 :===: t2) ::: _)
            | stuck t1 || stuck t2 -> tell (Set.singleton c)
            | otherwise            -> fail ("unsimplifiable constraint: " ++ pretty c)

        stuck (Free (Meta _) :$ _) = True
        stuck _                    = False

hetToHom :: HetConstraint -> Set.Set HomConstraint
hetToHom (ctx :|-: tm1 ::: ty1 :===: tm2 ::: ty2) = Set.fromList
  -- FIXME: represent dependency of second on first
  [ ctx :|-: (ty1 :===: ty2) ::: Type
  , ctx :|-: (tm1 :===: tm2) ::: ty1
  ]

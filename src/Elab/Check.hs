{-# LANGUAGE DeriveFunctor, GeneralizedNewtypeDeriving #-}
module Elab.Check where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader
import qualified Data.Map as Map
import Elab.Name
import Elab.Term (Term(..), Typing(..))
import qualified Elab.Term as Term
import Prelude hiding (fail)

type Type = Term
type Context v = [Type v]
type Signature v = Map.Map v (Type v)

newtype Elab v a = Elab { runElab :: ReaderC (Context v) (ReaderC (Signature v) (ReaderC Gensym (FreshC (FailC VoidC)))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

bound :: Int -> Elab v (Type v)
bound i = Elab $ do
  ctx <- ask
  pure (ctx !! i)

free :: (Ord v, Show v) => v -> Elab v (Type v)
free v = Elab $ do
  sig <- ask
  maybe (fail ("Variable not in scope: " <> show v)) pure (Map.lookup v sig)

lam :: Type Gensym -> (Gensym -> Elab Gensym (Type Gensym)) -> Elab Gensym (Type Gensym)
lam ty body = Elab $ do
  x <- gensym ""
  Term.pi (x ::: ty) <$> runElab (body x)

type' :: Elab v (Type v)
type' = pure Type

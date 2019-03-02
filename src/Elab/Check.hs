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

type Type = Term Name
type Context = [Type]
type Signature = Map.Map Name Type

newtype Check a = Check { runCheck :: ReaderC Type (ReaderC Context (ReaderC Signature (ReaderC Gensym (FreshC (FailC VoidC))))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

newtype Infer a = Infer { runInfer :: ReaderC Context (ReaderC Signature (ReaderC Gensym (FreshC (FailC VoidC)))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

bound :: Int -> Infer Type
bound i = Infer $ do
  ctx <- ask
  pure (ctx !! i)

free :: Name -> Infer Type
free v = Infer $ do
  sig <- ask
  maybe (fail ("Variable not in scope: " <> show v)) pure (Map.lookup v sig)

lam :: Type -> (Name -> Check Type) -> Check Type
lam ty body = Check $ do
  x <- Gensym <$> gensym ""
  Term.pi (x ::: ty) <$> runCheck (body x)

type' :: Infer Type
type' = pure Type

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

newtype Check v a = Check { runCheck :: ReaderC (Context v) (ReaderC (Signature v) (ReaderC Gensym (FreshC (FailC VoidC)))) a }
  deriving (Applicative, Functor, Monad, MonadFail)

bound :: Int -> Check v (Type v)
bound i = Check $ do
  ctx <- ask
  pure (ctx !! i)

free :: (Ord v, Show v) => v -> Check v (Type v)
free v = Check $ do
  sig <- ask
  maybe (fail ("Variable not in scope: " <> show v)) pure (Map.lookup v sig)

lam :: Type Name -> (Name -> Check Name (Type Name)) -> Check Name (Type Name)
lam ty body = Check $ do
  x <- Gensym <$> gensym ""
  Term.pi (x ::: ty) <$> runCheck (body x)

type' :: Check v (Type v)
type' = pure Type

{-# LANGUAGE DeriveFunctor, GeneralizedNewtypeDeriving #-}
module Elab.Check where

import Control.Effect
import Control.Effect.Fail
import Control.Effect.Reader
import qualified Data.Map as Map
import Elab.Term (Term(..))
import Prelude hiding (fail)

type Type = Term

newtype Elab v a = Elab { runElab :: ReaderC [Type v] (ReaderC (Map.Map v (Type v)) (FailC VoidC)) a }
  deriving (Applicative, Functor, Monad, MonadFail)

bound :: Int -> Elab v (Type v)
bound i = Elab $ do
  ctx <- ask
  pure (ctx !! i)

free :: (Ord v, Show v) => v -> Elab v (Type v)
free v = Elab $ do
  sig <- ask
  maybe (fail ("Variable not in scope: " <> show v)) pure (Map.lookup v sig)

type' :: Elab v (Type v)
type' = pure Type

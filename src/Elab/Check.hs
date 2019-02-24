{-# LANGUAGE DeriveFunctor #-}
module Elab.Check where

import Control.Monad (ap)
import Control.Monad.Fail
import Elab.Term
import Prelude hiding (fail)

type Type = Term

newtype Elab v a = Elab { runElab :: [Type v] -> Either String a }
  deriving (Functor)

instance Applicative (Elab v) where
  pure a = Elab (const (Right a))
  (<*>) = ap

instance Monad (Elab v) where
  Elab a >>= f = Elab (\ ctx -> do
    a' <- a ctx
    runElab (f a') ctx)

instance MonadFail (Elab v) where
  fail s = Elab (const (Left s))

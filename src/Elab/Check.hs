{-# LANGUAGE DeriveFunctor #-}
module Elab.Check where

import Control.Monad (ap)
import Control.Monad.Fail
import qualified Data.Map as Map
import Elab.Term
import Prelude hiding (fail)

type Type = Term

newtype Elab v a = Elab { runElab :: [Type v] -> Map.Map v (Type v) -> Either String a }
  deriving (Functor)

instance Applicative (Elab v) where
  pure a = Elab (const (const (Right a)))
  (<*>) = ap

instance Monad (Elab v) where
  Elab a >>= f = Elab (\ ctx sig -> do
    a' <- a ctx sig
    runElab (f a') ctx sig)

instance MonadFail (Elab v) where
  fail s = Elab (const (const (Left s)))


bound :: Int -> Elab v (Type v)
bound i = Elab (\ ctx _ -> Right (ctx !! i))

type' :: Elab v (Type v)
type' = Elab (const (const (Right Type)))

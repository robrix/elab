{-# LANGUAGE TypeOperators #-}
module Elab.Check where

import Control.Monad.Fail
import Elab.Elab
import Elab.Name
import Elab.Term (Term(..), instantiate)
import Elab.Type (Type)
import Prelude hiding (fail, pi)

elab :: Term Name -> Elab (Value Meta ::: Type Meta)
elab (Head (Bound i)) = fail ("Unexpected bound variable " ++ show i)
elab (Head (Free v))  = assume v
elab (Lam b)          = intro (\ n -> elab (instantiate (pure n) b))
elab (f :$ a)         = elab f $$ elab a
elab Type             = type'
elab (Pi t b)         = pi (elab t) (\ n -> elab (instantiate (pure n) b))

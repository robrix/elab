{-# LANGUAGE TypeOperators #-}
module Elab.Check where

import Elab.Elab
import Elab.Name
import Elab.Term (Term(..), instantiate)
import Elab.Type (Type)
import Prelude hiding (fail, pi)

elab :: Term Name -> Elab (Value Meta ::: Type Meta)
elab (Var v)  = assume v
elab (Lam b)  = intro (\ n -> elab (instantiate (pure n) b))
elab (f :$ a) = elab f $$ elab a
elab Type     = type'
elab (Pi t b) = pi (fmap elab t) (\ n -> elab (instantiate (pure n) b))

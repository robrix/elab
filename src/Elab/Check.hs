{-# LANGUAGE TypeOperators #-}
module Elab.Check where

import Control.Monad.Fail
import Elab.Elab
import Elab.Name
import Elab.Term (Term(..), instantiate)
import Elab.Type (Type)
import Prelude hiding (fail, pi)

check :: Term Name -> Check (Value Name ::: Type Name)
check (Lam body) = intro (\ name -> check (instantiate (pure name) body))
check t          = switch (infer t)

infer :: Term Name -> Infer (Value Name ::: Type Name)
infer (Head (Bound i)) = fail ("Unexpected bound variable " ++ show i)
infer (Head (Free v))  = assume v
infer (f :$ a)         = infer f $$ check a
infer Type             = type'
infer (Pi t body)      = pi (check t) (\ name -> check (instantiate (pure name) body))
infer t                = fail ("No rule to infer type of term " ++ show t)

elab :: Term Name -> Elab (Value Meta ::: Type Meta)
elab (Head (Bound i)) = fail ("Unexpected bound variable " ++ show i)
elab (Head (Free v))  = assume' v
elab (Lam b)          = intro' (\ n -> elab (instantiate (pure n) b))
elab (f :$ a)         = elab f $$$ elab a
elab Type             = type''
elab (Pi t b)         = pi' (elab t) (\ n -> elab (instantiate (pure n) b))

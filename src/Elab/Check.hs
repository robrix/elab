module Elab.Check where

import Control.Monad.Fail
import Elab.Elab
import Elab.Name
import Elab.Term (Term(..), instantiate)
import Elab.Type (Typed(..))
import Prelude hiding (fail, pi)

check :: Term Name -> Check (Typed Name Value)
check (Lam body)       = introduce (\ name -> check (instantiate (pure name) body))
check t                = switch (infer t)

infer :: Term Name -> Infer (Typed Name Value)
infer (Head (Bound i)) = fail ("Unexpected bound variable " ++ show i)
infer (Head (Free v))  = assumption v
infer (f :$ a)         = infer f $$ check a
infer Type             = type'
infer (Pi t body)      = pi (check t) (\ name -> check (instantiate (pure name) body))
infer t                = fail ("No rule to infer type of term " ++ show t)

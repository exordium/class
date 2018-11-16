module Types (module Types, module X) where
import GHC.Types as X

type c ==> c' = (forall x. c x => c' x :: Constraint)

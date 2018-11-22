{-# language UndecidableSuperClasses #-}
module Types (module Types, module X) where
import GHC.Types as X

type c ==> c' = (forall x. c x => c' x :: Constraint)
type Lifting c c' t = (forall x. c x => c' (t x) :: Constraint)

class (c x, c' x) => (c :*: c') x
instance (c x, c' x) => (c :*: c') x

{-# language UndecidableSuperClasses #-}
module Types (module Types, module X) where
import GHC.Types as X

type f --> g = forall x. f x -> f g
type c ==> c' = (forall x. c x => c' x :: Constraint)
type Lifting c c' t = (forall x. c x => c' (t x) :: Constraint)

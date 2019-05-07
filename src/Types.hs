{-# language UndecidableSuperClasses #-}
{-# language CPP #-}
module Types (module Types, module X) where
import GHC.Types as X (Constraint,Ordering(..))
import GHC.Maybe as X (Maybe(..))

#include "HsBaseConfig.h"



type f --> g = forall x. f x -> f g
type c ==> c' = (forall x. c x => c' x :: Constraint)
type Lifting c c' t = (forall x. c x => c' (t x) :: Constraint)
class (c a, c' a) => (c & c') a
instance (c a, c' a) => (c & c') a

class Stock (a :: k)
instance Stock (a :: k)

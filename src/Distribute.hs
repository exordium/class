{-# language UndecidableInstances #-}
{-# language InstanceSigs #-}
module Distribute
  {-( Distribute(..), distribute-}
  {-, zipWithF_, zipWithF-}
  {-, collect_, collect-}
   where
import Map
import Coerce
import I
import Types
import qualified Prelude as P
import Impl
import Coercemap
import E
import IsEither
import K
import Def
import X
import Fun hiding ((!))


{-impl @Map    [t|[]|]             ! #map    [|P.map|]-}

class (c ==> Map, Map t) => Distribute c t where
  distribute :: c f => f (t a) -> t (f a)
  distribute = collect @c \ x -> x
  zipWithF   :: c f => (f a -> b) -> f (t a) -> t b
  zipWithF fab = \fta -> map fab (distribute @c fta)
  collect :: c f => (a -> t b) -> f a -> t (f b)
  collect f a = zipWithF @c (\x -> x) (map f a)


instance (c ==> Map, Map ((->) x)) => Distribute c ((->) x) where distribute fxa = \x -> map (\xa -> xa x) fxa

instance (c ==> Map, Map I) => Distribute c I where distribute (fia :: f (I a)) = I (coercemap unI fia)

instance Distribute IsEither [] where
  distribute = \case {L x -> [L x]; R ts -> map R ts}
  zipWithF fab = \case
    L x -> [fab (L x)]
    R ta -> map (\a -> fab (R a)) ta
  collect atb = \case
    L x -> [L x]
    R a -> map R (atb a)

instance (c ==> Map, Def a, Map (K a)) => Distribute c (K a) where distribute _ = K def

distribute_pure :: Distribute IsEither t => a -> t a
distribute_pure a = (id ||| absurd) `map` distribute @IsEither (L a)

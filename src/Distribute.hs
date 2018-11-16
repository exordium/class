{-# language UndecidableInstances #-}
{-# language InstanceSigs #-}
module Distribute
  ( Distribute(..), distribute
  , zipWithF_, zipWithF
  , collect_, collect
  ) where
import Map
import Coerce
import I
import Types
import qualified Prelude as P
import Impl
import Coercemap
import E
import IsEither

{-impl @Map    [t|[]|]             ! #map    [|P.map|]-}

class (Map t) => Distribute t where
  type C t :: (* -> *) -> Constraint
  {-distribute_' :: (forall ff. cc ff => c ff, cc f) => f (t a) -> t (f a)-}
  distribute_ :: (cc ==> C t, C t f, cc f) => f (t a) -> t (f a)
  {-distribute_ = zipWithF @t @(C t) \ x -> x-}


distribute :: forall t f a. (Distribute t, C t f) => f (t a) -> t (f a)
distribute = distribute_ @t @(C t)

zipWithF_ :: forall cc t f a b. (Distribute t,  cc ==> C t , C t f, cc f)
         => (f a -> b) -> f (t a) -> t b
zipWithF_ fab = \fta -> map fab (distribute_ @t @(C t) fta)

zipWithF :: forall t f a b. (Distribute t,  C t f)
         => (f a -> b) -> f (t a) -> t b
zipWithF fab = \fta -> map fab (distribute_ @t @(C t) fta)

collect_ :: forall cc t f a b. (Distribute t,  (forall ff. cc ff => (C t ff, Map ff))  , C t f, cc f)
        => (a -> t b) -> f a -> t (f b)
collect_ f a = distribute_ @t @(C t) (map f a)

collect :: forall t f a b. (Distribute t, C t f, Map f)
        => (a -> t b) -> f a -> t (f b)
collect f a = distribute_ @t @(C t) (map f a)
{-collect f a = distribute_ @t @(C t) (map f a)-}


instance Distribute ((->) x) where
  type C ((->) x) = Map
  distribute_ fxa = \x -> map (\xa -> xa x) fxa
  {-zipWithF :: (cc ==> Map , Map f, cc f) => (f a -> b) -> f (x -> a) -> x -> b-}
  {-zipWithF = P.undefined-}


instance Distribute I where
  type C I = Coercemap
  {-distribute_ :: forall c f a.  (c ==> Remap, c f) => f (I a) -> I (f a)-}
  distribute_ (fia :: f (I a)) = I (coercemap unI fia)

instance Distribute [] where
  type C [] = IsEither
  {-distribute_ :: (c ==> IsEither, IsEither t => t [a] -> [t a]-}
  distribute_ = \case {L x -> [L x]; R ts -> map R ts}

{-distribute :: forall t f a. (Distribute t, C t f) => f (t a) -> t (f a)-}
{-distribute = distribute_ @t @(C t)-}

{-# language UndecidableInstances #-}
{-# language InstanceSigs #-}
module Closed where
import Promap
import Pure
import Distribute
import Types
import IsEither
import qualified Prelude as P


{-class Promap p => Closed p where-}
  {-grate :: (((s -> a) -> b) -> t) -> p a b -> p s t-}
  {-{-grate f = \p -> promap (\a g -> g a) f (zipping zip p)-}-}
  {-zipping :: (forall f. Map f => (f a -> b) -> f s -> t) -> p a b -> p s t-}
  {-zipping sabsst = grate (`sabsst` \x -> x)-}
  {-distributed :: (C t ~ Map, Distribute t) => p a b -> p (t a) (t b)-}
  {-distributed = zipping zipWithF-}

class (Promap p, c ~ Map) => Zipping c p where
  distributed :: forall t a b. Distribute c t => p a b -> p (t a) (t b)
  distributed = zipping @c (zipWithF @c)
  closed :: p a b -> p (x -> a) (x -> b)
  closed = distributed
  grate :: (((s -> a) -> b) -> t) -> p a b -> p s t
  grate sa_b_t = \ab -> promap (\a g -> g a) sa_b_t (distributed @c ab)
  zipping :: (forall f. c f => (f a -> b) -> f s -> t) -> p a b -> p s t
  zipping sabsst = grate (`sabsst` \ s -> s)


instance c ~ Map => Zipping c (->) where
  zipping sabsst ab = promap (\a g -> g a) (`sabsst` \ s -> s) (map ab)
  distributed = map

weaken :: forall c' c r. (c' => c) => (c => r) -> (c' => r)
weaken f = f

weaken1 :: forall c' c x r. (c' ==> c) => (c x => r) -> (c' x => r)
weaken1 f = f

ff :: forall f. Map f => f Char -> f P.String
ff = map P.show

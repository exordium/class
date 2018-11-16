module Coercemap where
import Coerce

class Coercemap f where
  coercemap :: a =# b => (a -> b) -> f a -> f b
  default coercemap :: (Representational f, a =# b) => (a -> b) -> f a -> f b
  coercemap _ = coerce
  {-# INLINE coercemap #-}

module Optic.Traversing where
import Traverse
import Map
import Promap

newtype Traversing f a b = Traversing {runTraversing :: a -> f b}

_Traversing :: (Traversing f a b -> Traversing f s t) -> (a -> f b) -> s -> f t
_Traversing = promap Traversing runTraversing

instance Map f => Map (Traversing f a) where map f (Traversing afb) = Traversing (\a -> map f (afb a))
instance Remap f => Remap (Traversing f a) where remap f g (Traversing afb) = Traversing (\a -> remap f g (afb a))
instance Strong f => Strong (Traversing f a) where strong x (Traversing afb) = Traversing (\a -> strong x (afb a))

instance Map f => Promap (Traversing f) where
  promap pre post (Traversing xfy) = Traversing (\a -> map post (xfy (pre a)))
instance Map f => Postmap (Traversing f) where
  postmap f (Traversing xfy) = Traversing (\a -> map f (xfy a))
instance Premap (Traversing f) where
  premap f (Traversing xfy) = Traversing (\a -> (xfy (f a)))

instance Traversed () (Traversing f) where
  traversal afbsft (Traversing afb) = Traversing (afbsft afb)

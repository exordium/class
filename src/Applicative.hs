module Applicative (module Applicative, module X) where
import Map as X

class Map f => Pure f where pure :: a -> f a
class Map f => Apply f where ap :: f (a -> b) -> f a -> f b
class (Pure f, Apply f) => Applicative f
class Applicative f => Monad f where bind :: (a -> f b) -> f a -> f b

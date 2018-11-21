module Applicative (module Applicative, module X) where
import Map as X

class (Pure f, Apply f) => Applicative f
class Applicative f => Monad f where bind :: (a -> f b) -> f a -> f b

module Apply where

class Map f => Apply f where ap :: f (a -> b) -> f a -> f b

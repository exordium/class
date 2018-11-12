module Fun.Impl where

type P = (->)
promap :: (a -> x) -> (y -> b) -> (x -> y) -> a -> b
promap f g p = \a -> g (p (f a))

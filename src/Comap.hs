{-# language TemplateHaskell #-}
module Comap (Comap(..), module X) where
import Remap as X

class Remap f => Comap f where comap :: (b -> a) -> f a -> f b

instance Impl Comap where
  type Methods Comap = '["comap"]
  impl f (Arg comap) = [d|
    instance Comap $f where comap      = $comap
    instance Remap $f where remap f _  = $comap f
   |]

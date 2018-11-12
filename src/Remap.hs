{-# language TemplateHaskell #-}
module Remap (Remap(..), module X) where
import Impl as X

class Remap f where remap :: (b -> a) -> (a -> b) -> f a -> f b

instance Impl Remap where
  type Methods Remap = '["remap"]
  impl f (Arg remap) = [d|instance Remap $f where remap = $remap|]

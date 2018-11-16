{-# language TemplateHaskell #-}
module Premap (Premap(..), module X) where
import Impl as X hiding ((!))

class Premap f where premap :: (b -> a) -> f a x -> f b x

instance Impl Premap where
  type Methods Premap = '["premap"]
  impl p (Arg premap) = [d|instance Premap $p where premap  = $premap|]

instance Premap (->) where premap = \f p a -> p (f a)

{-# language TemplateHaskell #-}
{-# language QuasiQuotes #-}
module Postmap (Postmap(..), module X) where
import Map as X
import TV

class (forall x. Map (f x)) => Postmap f where
  postmap :: (a -> b) -> f x a -> f x b

instance Impl Postmap where
  type Methods Postmap = '["postmap"]
  impl p (Arg postmap) = [d|
    instance Postmap $p where postmap  = $postmap
    instance Map    ($p [tv|x|]) where map      = $postmap
    instance Strong ($p [tv|x|]) where strong a = $postmap ((,) a)
    instance Remap  ($p [tv|x|]) where remap _  = $postmap
   |]

instance Postmap (->) where postmap = map

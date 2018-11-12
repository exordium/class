
{-# language TemplateHaskell #-}
{-# language QuasiQuotes #-}
module Bimap (Bimap(..), module X) where
import LMap as X
import Postmap as X
import TV

class (LMap f, Postmap f) => Bimap f where bimap :: (x -> a) -> (y -> b) -> f x y -> f a b

instance Impl Bimap where
  type Methods Bimap = '["bimap"]
  impl p (Arg bimap) = [d|
    instance Bimap  $p where bimap   = $bimap
    instance LMap  $p where lmap f = $bimap f \ x -> x
    instance Postmap $p where postmap  = $bimap \ x -> x
    instance Map    ($p [tv|x|]) where map      = postmap
    instance Strong ($p [tv|x|]) where strong a = map ((,) a)
    instance Remap  ($p [tv|x|]) where remap _  = map
   |]

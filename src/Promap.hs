{-# language TemplateHaskell #-}
{-# language QuasiQuotes #-}
module Promap (Promap(..), module X) where
import Premap as X
import Postmap as X
import TV

class (Premap p, Postmap p) => Promap p where promap :: (a -> x) -> (y -> b) -> p x y -> p a b

instance Impl Promap where
  type Methods Promap = '["promap"]
  impl p (Arg promap) = [d|
    instance Promap  $p where promap   = $promap
    instance Premap  $p where premap f = $promap f \ x -> x
    instance Postmap $p where postmap  = $promap \ x -> x
    instance Map    ($p [tv|x|]) where map      = postmap
    instance Strong ($p [tv|x|]) where strong a = map ((,) a)
    instance Remap  ($p [tv|x|]) where remap _  = map
   |]

instance Promap (->) where promap = \f g p a -> g (p (f a))

{-# language MagicHash #-}
module Coerce.Map where
import Coerce
import Impl
import Map

instance Impl Coercemap where
  type Methods Coercemap = '["map"]
  impl f (Arg map) = [d|
    instance Coercemap $f
    instance Map    $f where map      = $map
    instance Strong $f where strong a = $map ((,) a)
    instance Remap  $f where remap _  = $map
   |]

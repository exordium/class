{-# language TemplateHaskell #-}
module LMap (LMap(..), module X) where
import Impl as X hiding ((!))

class LMap f where lmap :: (a -> b) -> f a x -> f b x

instance Impl LMap where
  type Methods LMap = '["lmap"]
  impl p (Arg lmap) = [d|instance LMap $p where lmap  = $lmap|]

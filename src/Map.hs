{-# language TemplateHaskell #-}
module Map (Map(..), module X) where
import E
import qualified Prelude as P
import Strong as X

class Strong f => Map f where
  map :: (a -> b) -> f a -> f b
  constMap :: b -> f a -> f b
  constMap b = map \ _ -> b

instance Impl Map where
  type Methods Map = '["map"]
  impl f (Arg map) = [d|
    instance Map    $f where map      = $map
    instance Strong $f where strong a = $map ((,) a)
    instance Remap  $f where remap _  = $map
   |]

instance Map ((->) x) where map f g = \a ->  f (g a)
instance Map [] where map = P.map
instance Map (E x) where map f = \case {L x -> L x; R a -> R (f a)}

{-# language TemplateHaskell #-}
module Strong (Strong(..),module X) where
import qualified Prelude as P
import E
import Remap  as X

class Remap f => Strong f where
  {-# minimal strong | strengthen #-}
  strong :: a -> f b -> f (a,b)
  strong = strengthen (\(a,_) -> a) (\(_,b) -> b) (,)
  strengthen :: (c -> a) -> (c -> b) -> (a -> b -> c) -> a -> f b -> f c
  strengthen f g h a fb = remap (\c -> (f c, g c)) (\(x,y) -> h x y) (strong a fb)
  fill :: a -> f () -> f a
  fill = strengthen (\a -> a) (\_ -> ()) (\a _ -> a)

instance Impl Strong where
  type Methods Strong = '["remap", "strong"]
  impl f (Arg remap) (Arg strong) = [d|
    instance Remap  $f where remap  = $remap
    instance Strong $f where strong = $strong
   |]

instance Strong [] where strong a = P.map (a,)
instance Strong ((->) x) where strong x g = \a -> (x,g a)
instance Strong (E x) where strong x = \case {L x -> L x; R a -> R (x,a)}

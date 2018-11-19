{-# language UndecidableSuperClasses #-}
{-# language UndecidableInstances #-}
{-# language EmptyCase #-}
module Pure where
import E
import Distribute
import Impl
import Map
import Types
import IsEither
import qualified Prelude as P
import K
import Traverse


class Distribute IsEither t => Pure t where
  pure :: a -> t a
  default pure :: a -> t a
  pure = \(a :: a) -> map (\case L a -> a) (distribute @IsEither (L a))
  {-pure a = map (\case L a -> a) (collect (\case{}) (L a))-}


instance Impl Pure where
  type Methods Pure = '["map", "pure"]
  impl f (Arg map) (Arg pure) = [d|
    instance Pure   $f where pure = $pure
    instance Map    $f where map      = $map
    instance Strong $f where strong a = $map ((,) a)
    instance Remap  $f where remap _  = $map
   |]

{-distribute = distribute_ @t @(C t)-}
  
instance Pure []
instance Pure ((->) x) where 

instance Pure (K ())

data Stream a = Stream {head :: a , tail :: Stream a}
instance P.Show a => P.Show (Stream a) where
  show s = P.show (head s) P.++ " : " P.++ P.show (tail s)
from n = Stream n (from (n P.+ 10))

impl @Map [t|Stream|] ! #map [|\f (Stream a as) -> Stream (f a) (map f as)|]
instance (c ==> Map, Map Stream) => Distribute c Stream where
  distribute = go where go fas = Stream (map head fas) (go (map tail fas))

instance Pure Stream

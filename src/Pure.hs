{-# language UndecidableSuperClasses #-}
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


class (c x, d x) => (c :*: d) x
instance  (c x, d x) => (c :*: d) x

class (Distribute t) => Pure t where
  pure :: a -> t a
  default pure :: C t (E a) => a -> t a
  pure = \(a :: a) -> map (\case L a -> a) (distribute (L a))
  {-pure a = map (\case L a -> a) (collect (\case{}) (L a))-}

pure' :: (C t (E a)) => Distribute t => a -> t a
pure' = \(a :: a) -> map (\case L a -> a) (distribute (L a))

{-distribute = distribute_ @t @(C t)-}
  
instance Pure []
instance Pure ((->) x) where 

class U a
instance U a
instance Distribute (K ()) where
  type C (K ()) = U
  distribute_ _ = K ()
instance Pure (K ())

{-instance Pure ((->) x) where pure x = \_ -> x-}
data Stream a = Stream {head :: a , tail :: Stream a}
instance P.Show a => P.Show (Stream a) where
  show s = P.show (head s) P.++ " : " P.++ P.show (tail s)
from n = Stream n (from (n P.+ 10))

impl @Map [t|Stream|] ! #map [|\f (Stream a as) -> Stream (f a) (map f as)|]
instance Distribute Stream where
  type C Stream = Map
  distribute_ = go where go fas = Stream (map head fas) (go (map tail fas))

instance Pure Stream

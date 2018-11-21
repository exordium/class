module FDot where
import Remap
import Map
import E
import Fun
import qualified Prelude as P
import List
import These

-- | A @Monoidal@ functor over some associative monoidal product @t@
class Remap f => Monoidal t f where monoidal :: f a -> f b -> f (a `t` b)


instance Monoidal (,) [] where monoidal as bs = (,) P.<$> as P.<*> bs
instance Monoidal E [] where monoidal as bs = map L as P.++ map R bs
instance Monoidal These [] where monoidal = list'align

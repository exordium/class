{-# language UndecidableSuperClasses #-}
module Functor.Monoidal where
import Functor
import Data
import Fun
import Type.X
import Type.List
import Type.These
import Type.E
import qualified Prelude as P
-- | A @Monoidal@ functor over some associative monoidal product @t@
class Remap f => Monoidal t f where monoidal :: f a -> f b -> f (a `t` b)

-- | Covariant E-monoidal functors can be appended
class (forall x. Add (f x), Monoidal E f, Map f) => Append f where
  append :: f a -> f a -> f a
  append fa fa' = map (\case L a -> a; R b -> b) (monoidal fa fa')

-- | fa |&| fb = map swap (fb |&| fa) TODO: Is this always useful?
-- f |&| empty = map This f
-- empty |&| g = map That g
class (Filter f, Monoidal These f) => Align f where
  zip :: f a -> f b -> f (a,b)
  {-zip fa fb = fmap (\case These a b -> Just (a,b); _ -> Nothing) $ align fa fb-}
  alignWith :: (a -> c) -> (b -> c) -> (a -> b -> c) -> f a -> f b -> f c
  alignWith f g h = \a b -> go `map` monoidal @These a b where
    go = \case
      This x -> f x
      That y -> g y
      These x y -> h x y
align :: Monoidal These f => f a -> f b -> f (These a b)
align = monoidal @These

class FTop f where ftop :: f ()


instance Monoidal (,) [] where monoidal as bs = [(a,b) | a <- as, b <- bs]
instance Monoidal E [] where monoidal as bs = map L as P.++ map R bs
instance Append []
instance Monoidal These [] where monoidal = list'align

instance Monoidal (,) ((->) x) where monoidal xa xb = \x -> (xa x, xb x)

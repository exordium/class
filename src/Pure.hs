{-# language UndecidableSuperClasses #-}
{-# language UndecidableInstances #-}
{-# language EmptyCase #-}
module Pure where
import E
import Impl
import Map
import Types
import IsEither
import qualified Prelude as P
import K
import Fun hiding ((!))
import Add
import Mul
import I


-- | A @Pure f@ is a pointed functor with a particular inhabited shape singled out
class (Lifting Zero One f, Remap f) => Pure f where
  fone :: f ()
  fone = pure ()
  pure :: a -> f a
  pure a = remap (\_ -> ()) (\_ -> a) fone

-- |A @Pure f@ distributes through Sum types:
--  http://r6research.livejournal.com/28338.html
instance {-# Overlappable #-} (Pure t, Zero x) => One (t x) where one = pure zero

pure_distribute :: (Map t, Pure t) => E x (t a) -> t (E x a)
pure_distribute = (pure < L) ||| map R

instance Impl Pure where
  type Methods Pure = '["remap", "pure"]
  impl f (arg #remap -> r) (arg #pure -> p) = [d|
    instance Pure   $f where pure = $p
    instance Remap  $f where remap _  = $r
   |]

instance Pure [] where pure a = [a]
instance Zero a => Pure (K a) where pure _ = K zero


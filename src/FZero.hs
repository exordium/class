module FZero where
import X
import Remap
import Map
import Add

-- | A @FZero f@ is a functor with a particular empty shape singled out
-- Dual to 'Pure'
class (Remap f, Zero (f X)) => FZero f where
  fzero :: f X
  fzero = lose (\x -> x)
  lose :: (a -> X) -> f a
  lose f = remap f absurd fzero

instance FZero [] where fzero = []

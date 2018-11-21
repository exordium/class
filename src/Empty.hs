module Empty where
import Map
import Add

-- | 'FZero' which are also 'Map' can be 'empty' for any type.
-- Default may be overriden with a more efficient version.
class (Map f, FZero f, forall x. Zero (f x)) => Empty f where
  empty :: f a
  empty = map absurd fzero

instance Empty []
instance {-# Overlappable #-} Empty f => Zero (f x) where zero = empty


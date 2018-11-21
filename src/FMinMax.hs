module FMinMax where
import FDot
import These
import Map

-- | fa |&| fb = map swap (fb |&| fa) TODO: Is this always useful?
-- f |&| empty = map This f
-- empty |&| g = map That g
class (Monoidal These f, Map f) => Align f where
  {-# minimal alignWith | align #-}
  align :: f a -> f b -> f (These a b)
  align = alignWith This That These
  alignWith :: (a -> c) -> (b -> c) -> (a -> b -> c) -> f a -> f b -> f c
  alignWith f g h = \a b -> go `map` align a b where
    go = \case
      This x -> f x
      That y -> g y
      These x y -> h x y

class FTop f where ftop :: f ()

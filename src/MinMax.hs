module MinMax where
import qualified Prelude as P

class Min' a where
  min' :: a -> a -> P.Maybe a
  minable :: a -> a -> P.Bool
-- | A @min@ is idempotent, commutative, and associative
-- prop> a `min` a = a
-- prop> (a `min` b) `min` c = a `min` (b `min` c)
-- prop> a `min` b = b `min` a
class Min  a where min  :: a -> a -> a

class Max' a where
  max' :: a -> a -> P.Maybe a
  maxable :: a -> a -> P.Bool
class Max  a where max  :: a -> a -> a

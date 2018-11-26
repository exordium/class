{-# language UndecidableInstances #-}
module Data where
import qualified Data.Coerce as GHC
import qualified Prelude as P

-- | A distinguished value
class Zero a where zero :: a
-- | An associative Operation
class Add a where add :: a -> a -> a
-- | `zero` is the identity for `add`
class (Zero a, Add a) => Add0 a

-- | A distinguished value
class One a where one :: a
-- | An associative operation
class Mul a where mul :: a -> a -> a
-- | `one` is the identity for `mul`
class (One a, Mul a) => Mul1 a

-- | A @min@ is idempotent, commutative, and associative
-- prop> a `min` a = a
-- prop> (a `min` b) `min` c = a `min` (b `min` c)
-- prop> a `min` b = b `min` a
class Min  a where min  :: a -> a -> a
class Max  a where max  :: a -> a -> a

-- | Representational equality
type (=#) = GHC.Coercible
coerce :: b =# a => a -> b
coerce = GHC.coerce; {-# INLINE coerce #-}


-- * Instances

instance Zero () where zero = ()
instance Add () where add () () = ()
instance Add0 ()
instance Zero [x] where zero = []
instance Add [x] where add = (P.++)
{-instance {-# overlappable #-} P.Num a => Zero a where zero = P.fromInteger 0-}
{-instance {-# overlappable #-} P.Num a => Add a where add = (P.+)-}
{-instance {-# overlappable #-} P.Num a => Add0 a-}

instance Zero a => One [a] where one = [zero]
instance Add a => Mul [a] where mul as bs = [add a b | a <- as, b <- bs] 
instance Add0 a => Mul1 [a]

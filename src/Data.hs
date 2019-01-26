{-# language UndecidableInstances #-}
{-# language UndecidableSuperClasses #-}
{-# language ImpredicativeTypes #-}
module Data where
import Types
import qualified Data.Coerce as GHC
import qualified Prelude as P

-- | A distinguished value
class Def a where def :: a
-- | An associative Semigrouperation
class Act a a => Semigroup a -- where op :: a -> a -> a
op :: Semigroup a => a -> a -> a
op = act
-- | a . def = def . a = a
class (Def a, Semigroup a) => Monoid a

class c a => Idempotent c a
class c a => Commutative c a

class T
instance T
class F

-- | Representational equality
type (=#) = GHC.Coercible
coerce :: b =# a => a -> b
coerce = GHC.coerce; {-# INLINE coerce #-}

class Ord' a where
  (<=) :: a -> a -> Bool
  --(<!) :: a -> a -> Bool
  --comparable :: a -> a -> Bool
instance Ord' Int where (<=) = (P.<=)
instance Ord Int
instance Act Int Int where act = (P.+)
instance Semigroup Int
instance Def Int where def = 0
instance Monoid Int
class Ord' a => Ord a

newtype Op (c :: * -> Constraint) a = Op a
  deriving P.Show
instance Ord' a => Ord' (Op Ord' a) where
  Op a <= Op b = b <= a
  --Op a <! Op b = b <! a
instance Semigroup a => Semigroup (Op Semigroup a)
instance Act a a => Act (Op Semigroup a) (Op Semigroup a) where
  Op a `act` Op b = Op (b `op` a)
deriving newtype  instance Def a    => Def    (Op Semigroup a)
deriving anyclass instance Monoid a => Monoid (Op Semigroup a) 

newtype Min a = Min a
  deriving newtype (Ord', Ord)
instance Semigroup (Min Int)
instance Act (Min Int) (Min Int)
  where act (Min a) (Min b) = Min (P.min a b)
instance Idempotent Semigroup (Min Int)
instance Commutative Semigroup (Min Int)
instance Semilattice (Min Int)

instance Semigroup (Max Int)
instance Act (Max Int) (Max Int)
  where act (Max a) (Max b) = Max (P.max a b)
instance Idempotent Semigroup (Max Int)
instance Commutative Semigroup (Max Int)
instance Semilattice (Max Int)

type Max a = Op Ord' (Min a)
pattern Max :: a -> Max a
pattern Max a = Op (Min a)

(&&) :: forall a. Semilattice (Min a) => a -> a -> a
(&&) = coerce (op @(Min a))
(||) :: forall a. Semilattice (Max a) => a -> a -> a
(||) = coerce (op @(Max a))

newtype GCD a = GCD a
instance Ord' (GCD Int) where GCD a <= GCD b = P.mod b a P.== 0
instance Ord (GCD Int)
instance Semigroup (GCD Int)
instance Act (GCD Int) (GCD Int) where act = coerce (P.gcd @Int)
instance Def (GCD Int) where def = coerce (0::Int)
instance Monoid (GCD Int)
instance Commutative Semigroup (GCD Int)
instance Idempotent Semigroup (GCD Int)
instance Semilattice (GCD Int)

type LCM a = Op Ord' (GCD a)
pattern LCM :: a -> LCM a
pattern LCM a = (Op (GCD a))

instance Semigroup (LCM Int) where
instance Act (LCM Int) (LCM Int) where act = coerce (P.lcm @Int)
instance Def (LCM Int) where def = coerce (1::Int)
instance Monoid (LCM Int)
instance Commutative Semigroup (LCM Int)
instance Idempotent Semigroup (LCM Int)
instance Semilattice (LCM Int)

instance Lattice (GCD Int)

-- | A near semiring (bi)module X..
--   (r*s)a = r(sa)
--   r(as) = (ra)s
--   (r+s)a = ra + sa
--   r(a+b) = ra + rb
class (Rg r, Semigroup a) => Scale r a where scale :: r -> a -> a

-- | Near Semiring. Ie a "Ring" without the Identity and Negation
-- a(b + c) = ab + ac
-- (a + b)c = ac + bc
-- so that: (x+y)(s+t) := xs + ys + xt + yt = xs + xt + ys + yt
class Scale a a => Rg a

-- | A semigroup action: (m+n)s = m(ns)
--  Acts like scalar offset
class Semigroup a => Act a s where act :: a -> s -> s

-- | Min semilattice
--   a . b <= a
--   a . b <= b
--   a . a == a
--   a . b == meet b a
class (Ord' a, Idempotent Semigroup a, Commutative Semigroup a)
  => Semilattice a
-- | meet a (join a b) = join a (meet a b) = a
class (Semilattice a, Semilattice (Op Ord' a)) => Lattice a
  


-- * Instances

instance Def () where def = ()
instance Semigroup ()
instance Act () () where () `act` () = ()
instance Monoid ()
instance Def [x] where def = []
instance Semigroup [x]
instance Act [x] [x] where act = (P.++)
instance Monoid [x]
{-instance {-# overlappable #-} P.Num a => Zero a where zero = P.fromInteger 0-}
{-instance {-# overlappable #-} P.Num a => Add a where add = (P.+)-}
{-instance {-# overlappable #-} P.Num a => Add0 a-}
newtype Default (c :: * -> Constraint)
                (c' :: * -> Constraint) 
                (a :: *)
                = Default a
newtype Mul a = Mul a

instance Def a => Def (Mul [a]) where def = Mul [def]
instance Semigroup a => Semigroup (Mul [a])
instance Act a a => Act (Mul [a]) (Mul [a])
  where Mul as `act` Mul bs = Mul [a `act` b | a <- as, b <- bs] 
instance Monoid a => Monoid (Mul [a])
--instance Add0 a => Mul1 [a]

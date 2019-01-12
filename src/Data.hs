{-# language UndecidableInstances #-}
{-# language TypeSynonymInstances #-}
{-# language UndecidableSuperClasses #-}
module Data where
import qualified Data.Coerce as GHC
import Types
import Data.Maybe as P
import qualified Prelude as P hiding ((.))
class Eq' a where
  {-# minimal eq' | comparable, eq #-}
  eq' :: a -> a -> P.Maybe Bool
  eq' a b = if comparable a b then P.Just (eq a b) else P.Nothing
  eq :: a -> a -> Bool
  eq a b = case eq' a b of
    P.Just True -> True
    _ -> False
  comparable :: a -> a -> Bool
  comparable a b = case eq' a b of
    P.Nothing -> False
    _ -> True
  ne :: a -> a -> Bool
  ne a b = P.not (eq a b)

-- | comparable = True
--   eq' a b = P.Just (eq a b)
class Eq' a => Eq a
class Eq' a => Ord' a where
  {-# minimal ord' | (<=) | (>=) #-}
  (<=), (>=), (<!), (>!) :: a -> a -> Bool
  a <= b = case ord' b a of {P.Just LT -> True; P.Just EQ -> True; _ -> False}
  a >= b = case ord' a b of {P.Just GT -> True; P.Just EQ -> True; _ -> False}
  a >! b = a <= b P.&& P.not (b <= a)
  a <! b = b >! a

  (<=?), (<?), (>?), (>=?) :: a -> a -> Maybe Bool
  a <=? b = if | a <= b -> P.Just True
               | b <= a -> P.Just False
               | True -> P.Nothing
  a >=? b = b <=? a
  a <? b = (a <= b) `go` (b <= a)
    where
          go False False = P.Nothing
          go True False = P.Just True
          go _ _ = P.Just False
  a >? b = b <? a
  ord' :: a -> a -> P.Maybe Ordering
  ord' a b = (a >= b) `go` (b >= a) where
    go True True = P.Just EQ
    go True False = P.Just GT
    go False True = P.Just LT
    go False False = P.Nothing
  comparable' :: a -> a -> Bool
  comparable' a b = (a <= b) P.|| (b <= a)

class Ord' a => Ord a where ord :: a -> Ordering

newtype Stock a = Stock a
  deriving newtype P.Num
instance P.Eq a => Eq (Stock a)
instance P.Eq a => Eq' (Stock a) where
  eq = coerce ((P.==) @a)
  ne = coerce ((P./=) @a)
  comparable _ _ = True
instance P.Ord a => Ord' (Stock a) where
  (<=) = coerce ((P.<=) @a)
  (<!) = coerce ((P.<) @a)
  (>=) = coerce ((P.>=) @a)
  (>!) = coerce ((P.>) @a)
  ord' (Stock a) (Stock b) = P.Just (P.compare a b)
{-instance P.Ord a => Meet (Inf (Stock a)) where (/\) = coerce (P.min @a)-}
instance P.Ord a => Op  (Inf (Stock a)) where (.) = coerce (P.min @a)
instance P.Ord a => Op  (Sup (Stock a)) where (.) = coerce (P.max @a)
instance P.Bounded a => Nil (Inf (Stock a)) where nil = coerce (P.maxBound @a)
instance P.Bounded a => Nil (Sup (Stock a)) where nil = coerce (P.minBound @a)
instance (P.Bounded a, P.Ord a) => Monoid (Inf (Stock a))
instance (P.Bounded a, P.Ord a) => Monoid (Sup (Stock a))

max :: forall a. Monoid (Inf a) => a
max = coerce (nil @(Inf a))
min :: forall a. Monoid (Sup a) => a
min = coerce (nil @(Sup a))
top :: forall a. Monoid (Meet a) => a
top = coerce (nil @(Meet a))
bot :: forall a. Monoid (Join a) => a
bot = coerce (nil @(Join a))

newtype Meet a = Meet a deriving newtype P.Num
newtype Join a = Join a deriving newtype P.Num
instance P.Integral a => Op (Meet (Stock a)) where (.) = coerce (P.gcd @a)
instance P.Integral a => Op (Join (Stock a)) where (.) = coerce (P.lcm @a)
instance P.Integral a => Nil (Meet (Stock a)) where nil = Meet 0
instance P.Integral a => Nil (Join (Stock a)) where nil = Join 1
instance P.Integral a => Monoid (Meet (Stock a))
instance P.Integral a => Monoid (Join (Stock a))
instance P.Integral a => Idempotent (Meet (Stock a))
instance P.Integral a => Idempotent (Join (Stock a))
instance P.Integral a => Commutative (Meet (Stock a))
instance P.Integral a => Commutative (Join (Stock a))
instance P.Integral a => Eq' (Meet (Stock a)) where
  eq' (Meet (Stock a)) (Meet (Stock b)) = P.Just (a P.== b)
instance P.Integral a => Ord' (Meet (Stock a)) where
  Meet (Stock a) <= Meet (Stock b) = P.mod b a P.== 0
{-instance P.Integral a => Join (Join (Stock a))-}

newtype Inf a = Inf a deriving newtype P.Num
{-instance Meet a => Op (Inf a) where (.) = coerce ((/\) @a)-}
newtype Sup a = Sup a deriving newtype P.Num
{-instance Join a => Op (Sup a) where (.) = coerce ((\/) @a)-}


-- | prop> a . a = a
class Op a => Idempotent a
-- | prop> a . b = b . a
class Op a => Commutative a


newtype Co a = Co a deriving newtype Eq'
instance Ord' a => Ord' (Co a) where
  (<=) = coerce ((>=) @a)
  (>=) = coerce ((<=) @a)
  (<=?) = coerce ((>=?) @a)
  (>=?) = coerce ((<=?) @a)
  (<!) = coerce ((>!) @a)
  (>!) = coerce ((<!) @a)
  (<?) = coerce ((>?) @a)
  (>?) = coerce ((<?) @a)
  ord' a b = coerce (ord' @a) b a
  comparable' = coerce (comparable' @a)

-- | A @(/\)@ is idempotent, commutative, and associative
-- prop> (a . b) <= a
-- prop> (a . b) <= b
class (Idempotent a, Commutative a, Ord' a) => Semilattice a
(/\) :: forall a. Semilattice (Meet a) => a -> a -> a
(/\) = coerce ((.) @(Meet a))
(\/) :: forall a. Semilattice (Join a) => a -> a -> a
(\/) = coerce ((.) @(Join a))
(&&) :: forall a. Semilattice (Inf a) => a -> a -> a
(&&) = coerce ((.) @(Inf a))
(||) :: forall a. Semilattice (Sup a) => a -> a -> a
(||) = coerce ((.) @(Sup a))
-- |Absorption: a \/ (a /\ b) == a /\ (a \/ b) == a
-- Implies: top \/ a = top, bottom /\ a = bottom
class (Semilattice a, Semilattice (Co a)) => Lattice a
-- | top /\ a = a
{-class Meet a => Top a where top :: a-}
-- | bottom \/ = a
{-class Join a => Bottom a where bottom :: a-}

deriving via (Stock Double) instance Eq' Double
deriving via (Stock Double) instance Ord' Double
{-deriving via (Stock Double) instance Meet Double-}
{-deriving via (Stock Double) instance Join Double-}
{-instance Lattice Double-}
{-instance Bottom Double where bottom = -1 P./ 0-}
{-instance Top Double    where top    =  1 P./ 0-}

class Op a where (.) :: a -> a -> a
class Nil a where nil :: a
class (Op a, Nil a) => Monoid a

newtype Add a = Add a
  deriving newtype P.Num
(+) :: forall a. Op (Add a) => a -> a -> a
(+) = coerce ((.) @(Add a))
zero :: forall a. Monoid (Add a) => a
zero = coerce (nil @(Add a))
newtype Mul a = Mul a
(*) :: forall a. Op (Mul a) => a -> a -> a
(*) = coerce ((.) @(Mul a))
one :: forall a. Monoid (Mul a) => a
one = coerce (nil @(Mul a))

{--- | A distinguished value-}
{-class Zero a where zero :: a-}
{--- | An associative Operation-}
{-class Add a where add :: a -> a -> a-}
{--- | `zero` is the identity for `add`-}
{-class (Zero a, Add a) => Add0 a-}

{--- | A distinguished value-}
{-class One a where one :: a-}
{--- | An associative operation-}
{-class Mul a where mul :: a -> a -> a-}
{--- | `one` is the identity for `mul`-}
{-class (One a, Mul a) => Mul1 a-}

{-class Inf  a where min  :: a -> a -> a-}
{-class Sup  a where max  :: a -> a -> a-}

-- | Representational equality
type (=#) = GHC.Coercible
coerce :: b =# a => a -> b
coerce = GHC.coerce; {-# INLINE coerce #-}


{--- * Instances-}

instance Op     () where _ . _ = ()
instance Nil    () where nil = ()
instance Monoid ()
instance Op     (Add [x]) where (.) = coerce ((P.++) @x)
instance Nil    (Add [x]) where nil = Add []
instance Monoid (Add [x])
instance Op a  => Op  (Mul [a]) where
  (.) = coerce \ as bs -> [(a::a) . b | a <- as, b <- bs]
instance Nil a => Nil (Mul [a]) where nil = Mul [nil]
instance Monoid a => Monoid (Mul [a])
instance P.Num a => Op     (Add (Stock a)) where (.) = coerce ((P.+) @a)
instance P.Num a => Op     (Mul (Stock a)) where (.) = coerce ((P.*) @a)
instance P.Num a => Nil    (Add (Stock a)) where nil = coerce (P.fromInteger @a 0)
instance P.Num a => Nil    (Mul (Stock a)) where nil = coerce (P.fromInteger @a 1)
instance P.Num a => Monoid (Add (Stock a)) 
instance P.Num a => Monoid (Mul (Stock a))

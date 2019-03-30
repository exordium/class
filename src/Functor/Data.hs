{-# language MagicHash #-}
module Functor.Data where
import Data
import Functor
import Control
import Type.E
import Type.I
import Fun
import qualified Data.Type.Equality as GHC
import qualified Prelude as P
import qualified Numeric.Natural as P
import Types

newtype Endo a = Endo (a -> a) deriving MapRep via Representational ## Endo
instance Remap Endo where remap ba ab (Endo aa) = Endo $ ba > aa > ab
instance FZero Endo where fzero = Endo (\case{})
instance Monoidal (,) Endo where monoidal (Endo aa) (Endo bb) = Endo \ (a,b) -> (aa a,bb b)
instance Monoidal E Endo where monoidal (Endo aa) (Endo bb) = Endo $ bimap aa bb

instance Category (GHC.:~:)
instance Identity (GHC.:~:) where identity = GHC.Refl
instance Compose (GHC.:~:) where compose = GHC.trans



instance P.Ord a => Act (Stock # Min a)  (Stock # Min a) where act = coerce (P.min @a)
instance P.Ord a => Semigroup  (Stock # Min a) where (.) = coerce (P.min @a)
instance P.Ord a => Idempotent  (Stock # Min a)
instance P.Ord a => Commutative  (Stock # Min a)
instance P.Ord a => Semilattice (Stock # Min a)
instance P.Bounded a => Nil (Stock # Min a) where nil = coerce (P.maxBound @a)
instance (P.Bounded a, P.Ord a) => Monoid (Stock # Min a)

{-instance P.Ord a => Act (Max (Stock a))  (Max (Stock a)) where act = coerce (P.max @a)-}
{-instance P.Ord a => Semigroup  (Max (Stock a)) -- where (.) = coerce (P.min @a)-}
{-instance P.Ord a => Idempotent  (Max (Stock a))-}
{-instance P.Ord a => Commutative  (Max (Stock a))-}
{-instance P.Ord a => Semilattice (Max (Stock a))-}
{-instance P.Bounded a => Nil (Max (Stock a)) where nil = coerce (P.minBound @a)-}
{-instance (P.Bounded a, P.Ord a) => Monoid (Max (Stock a))-}
{-instance P.Ord a => Lattice (Stock # Min a)-}

{-instance P.Integral a => Semigroup (GCD (Stock a)) -- where (.) = coerce (P.gcd @a)-}
{-instance P.Integral a => Act (GCD (Stock a)) (GCD (Stock a)) where act= coerce (P.gcd @a)-}
{-instance P.Integral a => Semigroup (LCM (Stock a)) -- where (.) = coerce (P.lcm @a)-}
{-instance P.Integral a => Act (LCM (Stock a)) (LCM (Stock a))-}
  {-where act = coerce (P.lcm @a)-}
{-instance P.Integral a => Nil (GCD (Stock a)) where nil = GCD 0-}
{-instance P.Integral a => Nil (LCM (Stock a)) where nil = LCM 1-}
{-instance P.Integral a => Monoid (GCD (Stock a))-}
{-instance P.Integral a => Monoid (LCM (Stock a))-}
{-instance P.Integral a => Idempotent (GCD (Stock a))-}
{-instance P.Integral a => Idempotent (LCM (Stock a))-}
{-instance P.Integral a => Commutative (GCD (Stock a))-}
{-instance P.Integral a => Commutative (LCM (Stock a))-}
{-instance P.Integral a => Eq' (GCD (Stock a)) where-}
  {-eq' (GCD (Stock a)) (GCD (Stock b)) = P.Just (a P.== b)-}
{-instance P.Integral a => Ord' (GCD (Stock a)) where-}
  {-GCD (Stock a) <= GCD (Stock b) = P.mod b a P.== 0-}

{-deriving via (Stock Double) instance Eq' Double-}
{-deriving via (Stock Double) instance Ord' Double-}

{-instance P.Num a => Semigroup     (Stock a) -- where (.) = coerce ((P.+) @a)-}
{-instance P.Num a => Act (Stock a) (Stock a) where act = coerce ((P.+) @a)-}
{-instance P.Num a => Scale  (Stock a) (Stock a) where scale = coerce ((P.*) @a)-}
{-instance P.Num a => Rg     (Stock a)-}
{-instance P.Num a => Nil    (Stock a) where nil = coerce (P.fromInteger @a 0)-}
{-instance P.Num a => Nil    (Mul (Stock a)) where nil = coerce (P.fromInteger @a 1)-}
{-instance P.Num a => Monoid (Stock a) -}
{-instance P.Num a => Monoid (Mul (Stock a))-}

newtype GCD a = GCD a deriving newtype P.Num
type LCM a = Op (GCD a)
pattern LCM :: a -> LCM a
pattern LCM a = Op (GCD a)

newtype Min a = Min a deriving newtype (P.Num, Ord', Eq',P.Show, P.Ord, P.Eq)
{-instance Meet a => Semigroup (Min a) where (.) = coerce ((/\) @a)-}
type Max a = Op (Min a)
pattern Max :: a -> Max a
pattern Max a = Op (Min a)
{-instance Join a => Semigroup (Max a) where (.) = coerce ((\/) @a)-}

(&&) :: forall a. Semilattice (Min a) => a -> a -> a
(&&) = coerce ((.) @(Min a))
(||) :: forall a. Semilattice (Max a) => a -> a -> a
(||) = coerce ((.) @(Max a))

max :: forall a. Monoid (Min a) => a
max = coerce (nil @(Min a))
min :: forall a. Monoid (Max a) => a
min = coerce (nil @(Max a))

deriving newtype instance Nil a => Nil (I a)
deriving newtype instance Monoid a => Monoid (I a)
instance Semigroup a => Act (I a) (I a) where act (I a) (I b) = I (act a b)
deriving newtype instance Semigroup a => Semigroup (I a)

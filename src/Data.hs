{-# language UndecidableInstances #-}
{-# language MagicHash #-}
{-# language TypeSynonymInstances #-}
{-# language UndecidableSuperClasses #-}
module Data where
import qualified Data.Coerce as GHC
import Types
import Data.Maybe as P
import qualified Prelude as P hiding ((.))
import qualified Numeric.Natural as P
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
  a <= b = case ord' a b of {P.Just LT -> True; P.Just EQ -> True; _ -> False}
  a >= b = case ord' a b of {P.Just GT -> True; P.Just EQ -> True; _ -> False}
  a >! b = b <= a P.&& P.not (a <= b)
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

instance Eq' a => Eq' [a] where
  eq' [] [] = Just True
  eq' (x:xs) (y:ys) | eq x y = eq' xs ys
  eq' _ _ = Just False
instance Ord' a => Ord' [a] where
  ord' []     []     = Just EQ
  ord' []     (_:_)  = Just LT
  ord' (_:_)  []     = Just GT
  ord' (x:xs) (y:ys) = case ord' x y of
                              Just EQ -> ord' xs ys
                              other -> other

class Ord' a => Ord a where ord :: a -> Ordering

newtype Stock a = Stock a
  deriving newtype (P.Num,P.Show)
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
{-instance P.Ord a => Meet (Min (Stock a)) where (/\) = coerce (P.min @a)-}
instance P.Ord a => Act (Min (Stock a))  (Min (Stock a)) where act = coerce (P.min @a)
instance P.Ord a => Semigroup  (Min (Stock a)) -- where (.) = coerce (P.min @a)
instance P.Ord a => Idempotent  (Min (Stock a))
instance P.Ord a => Commutative  (Min (Stock a))
instance P.Ord a => Semilattice (Min (Stock a))
instance P.Bounded a => Nil (Min (Stock a)) where nil = coerce (P.maxBound @a)
instance (P.Bounded a, P.Ord a) => Monoid (Min (Stock a))

instance P.Ord a => Act (Max (Stock a))  (Max (Stock a)) where act = coerce (P.max @a)
instance P.Ord a => Semigroup  (Max (Stock a)) -- where (.) = coerce (P.min @a)
instance P.Ord a => Idempotent  (Max (Stock a))
instance P.Ord a => Commutative  (Max (Stock a))
instance P.Ord a => Semilattice (Max (Stock a))
instance P.Bounded a => Nil (Max (Stock a)) where nil = coerce (P.minBound @a)
instance (P.Bounded a, P.Ord a) => Monoid (Max (Stock a))

{-instance Act (Min a) (Min a) => Act (Min [a]) (Min [a]) where-}
  {-act (Min []) _ = Min []-}
  {-act _ (Min []) = Min []-}
  {-act (Min (a:as)) (Min (b:bs)) = act a b : act (Min as) (Min bs)-}

instance P.Ord a => Lattice (Min (Stock a))


newtype GCD a = GCD a deriving newtype P.Num
type LCM a = Op (GCD a)
pattern LCM :: a -> LCM a
pattern LCM a = Op (GCD a)
instance P.Integral a => Semigroup (GCD (Stock a)) -- where (.) = coerce (P.gcd @a)
instance P.Integral a => Act (GCD (Stock a)) (GCD (Stock a)) where act= coerce (P.gcd @a)
instance P.Integral a => Semigroup (LCM (Stock a)) -- where (.) = coerce (P.lcm @a)
instance P.Integral a => Act (LCM (Stock a)) (LCM (Stock a))
  where act = coerce (P.lcm @a)
instance P.Integral a => Nil (GCD (Stock a)) where nil = GCD 0
instance P.Integral a => Nil (LCM (Stock a)) where nil = LCM 1
instance P.Integral a => Monoid (GCD (Stock a))
instance P.Integral a => Monoid (LCM (Stock a))
instance P.Integral a => Idempotent (GCD (Stock a))
instance P.Integral a => Idempotent (LCM (Stock a))
instance P.Integral a => Commutative (GCD (Stock a))
instance P.Integral a => Commutative (LCM (Stock a))
instance P.Integral a => Eq' (GCD (Stock a)) where
  eq' (GCD (Stock a)) (GCD (Stock b)) = P.Just (a P.== b)
instance P.Integral a => Ord' (GCD (Stock a)) where
  GCD (Stock a) <= GCD (Stock b) = P.mod b a P.== 0
{-instance P.Integral a => Join (Join (Stock a))-}

newtype Min a = Min a deriving newtype (P.Num, Ord', Eq',P.Show)
{-instance Meet a => Semigroup (Min a) where (.) = coerce ((/\) @a)-}
type Max a = Op (Min a)
pattern Max :: a -> Max a
pattern Max a = Op (Min a)
{-instance Join a => Semigroup (Max a) where (.) = coerce ((\/) @a)-}


-- | prop> a . a = a
class Semigroup a => Idempotent a
-- | prop> a . b = b . a
class Semigroup a => Commutative a


newtype Op a = Op a deriving newtype (Eq', P.Show)
instance Ord' a => Ord' (Op a) where
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

-- | Least upper bound
-- prop> (a . b) <= a
-- prop> (a . b) <= b
-- prop> forall x. (x <= a, x <= b) => x <= (a . b)
class (Idempotent a, Commutative a, Ord' a) => Semilattice a
{-(/\) :: forall a. Semilattice (Meet a) => a -> a -> a-}
{-(/\) = coerce ((.) @(Meet a))-}
{-(\/) :: forall a. Semilattice (Join a) => a -> a -> a-}
{-(\/) = coerce ((.) @(Join a))-}
(&&) :: forall a. Semilattice (Min a) => a -> a -> a
(&&) = coerce ((.) @(Min a))
(||) :: forall a. Semilattice (Max a) => a -> a -> a
(||) = coerce ((.) @(Max a))

max :: forall a. Monoid (Min a) => a
max = coerce (nil @(Min a))
min :: forall a. Monoid (Max a) => a
min = coerce (nil @(Max a))
{-top :: forall a. Monoid (Meet a) => a-}
{-top = coerce (nil @(Meet a))-}
{-bot :: forall a. Monoid (Join a) => a-}
{-bot = coerce (nil @(Join a))-}

-- |Absorption: a \/ (a /\ b) == a /\ (a \/ b) == a
-- Implies: top \/ a = top, bottom /\ a = bottom
class (Semilattice a, Semilattice (Op a)) => Lattice a
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

--  | act (diff x y) x = y
--    diff x y = inv (diff y x)
--    implies: diff x x = nil
class (Inv a, Act a x) => Diff a x where
  diff :: x -> x -> a
  default diff :: (x ~ a, Inv a) => x -> x -> a
  diff a b = a `act` inv b


class Act a a => Semigroup a where
  scale1 :: P.Natural -> a -> a
  scale1 n = scale1# (n P.+ 1) 

class Semigroup a => Act a s where act :: a -> s -> s
(.) :: Semigroup a => a -> a -> a
(.) = act
class Nil a where nil :: a
class (Semigroup a, Nil a) => Monoid a where
  scale0 :: P.Natural -> a -> a
  scale0 0 = \_ -> nil
  scale0 n = scale1# n

class (Monoid a, Diff a a) => Inv a where
  {-# minimal inv #-}
  inv :: a -> a
  inv = diff nil 
  scalei :: P.Integer -> a -> a
  scalei n a = case P.compare n 0 of
    EQ -> nil
    LT -> scale1# (P.fromInteger (P.abs n)) (inv a)
    GT -> scale1# (P.fromInteger n) a

-- | A (right) Near Semiring, Ie a "Ring" without the identity and negation
--(a+b)c = ac + bc
class Scale r r => Rg r

-- | A "Rig": Ring without negatives
class (Rg r, Monoid r, Monoid (Mul r)) => FromNatural r where
  fromNatural :: P.Natural -> r
  fromNatural = (`scale0` one)

-- | A Ring
class (FromNatural r, Inv r) => FromInteger r where
  fromInteger :: P.Integer -> r
  fromInteger = (`scalei` one)

-- | Scale by a non-zero @Natural@, this is not checked and will loop on 0.
scale1# :: Act a a => P.Natural -> a -> a
scale1# y0 x0 = f x0 y0 where
  f x y 
    | P.even y = f (x `act` x) (y `P.quot` 2)
    | y P.== 1 = x
    | P.otherwise = g (x `act` x) ((y P.- 1) `P.quot` 2) x
  g x y z 
    | P.even y = g (x `act` x) (y `P.quot` 2) z
    | y P.== 1 = x `act` z
    | P.otherwise = g (x `act` x) ((y P.- 1) `P.quot` 2) (x `act` z)



instance Rg r => Act (Mul r) (Mul r) where act (Mul a) (Mul b) = Mul (scale a b)
instance Rg r => Semigroup (Mul r)


-- | A near semiring (bi)module
-- (r*s)a = r(sa)
-- r(as) = (ra)s
-- (r+s)a = ra + sa
class (Rg r, Semigroup a) => Scale r a where scale :: r -> a -> a

newtype Add a = Add a
  deriving newtype P.Num
newtype Mul a = Mul a
(*) :: Rg r => r -> r -> r
(*) = scale
one :: forall a. Monoid (Mul a) => a
one = coerce (nil @(Mul a))

-- | Representational equality
type (=#) = GHC.Coercible
coerce :: b =# a => a -> b
coerce = GHC.coerce; {-# INLINE coerce #-}


{--- * Instances-}
instance Semigroup () -- where _ . _ = ()
instance Act    () () where _ `act` _ = ()
instance Nil       () where nil = ()
instance Monoid    ()
instance Semigroup [x] -- where (.) = coerce ((P.++) @x)
instance Act [x] [x]  where act = (P.++)
instance Nil [x]     where nil = []
{-instance Monoid (Add [x])-}
instance Semigroup a => Scale [a] [a] where
  scale as bs = [ a . b | a <- as, b <- bs]
instance Semigroup a  => Rg [a]
{-instance Act a s => Act  (Mul [a]) (Mul [s]) where-}
  {-act (Mul as) (Mul bs) = Mul [a `act` b | a <- as, b <- bs]-}
{-instance Nil a => Nil (Mul [a]) where nil = Mul [nil]-}
instance P.Num a => Semigroup     (Stock a) -- where (.) = coerce ((P.+) @a)
instance P.Num a => Act (Stock a) (Stock a) where act = coerce ((P.+) @a)
instance P.Num a => Scale  (Stock a) (Stock a) where scale = coerce ((P.*) @a)
instance P.Num a => Rg     (Stock a)
instance P.Num a => Nil    (Stock a) where nil = coerce (P.fromInteger @a 0)
instance P.Num a => Nil    (Mul (Stock a)) where nil = coerce (P.fromInteger @a 1)
instance P.Num a => Monoid (Stock a) 
instance P.Num a => Monoid (Mul (Stock a))

instance Semilattice (Min a) => Act (Min [a]) (Min [a])
  where act (Min as) (Min bs) = Min [x | Min x <- P.zipWith (.) [Min a | a <- as] [Min b | b <- bs]]
instance Semilattice (Min a) => Semigroup (Min [a])
instance Semilattice (Min a) => Idempotent (Min [a])
instance Semilattice (Min a) => Commutative (Min [a])
instance (Ord' a, Semilattice (Min a)) => Semilattice (Min [a])
instance (Monoid (Min a), Semilattice (Min a)) => Nil (Min [a])
  where nil = Min (let x = max : x in x)
instance (Monoid (Min a), Semilattice (Min a)) => Monoid (Min [a])

instance Semilattice (Max a) => Act (Max [a]) (Max [a]) where
  act (Max []) (Max bs) = Max bs
  act (Max as) (Max []) = Max as
  act (Max (a:as)) (Max (b:bs)) = coerce ((a || b) :) (act (Max as) (Max bs))
instance Semilattice (Max a) => Semigroup (Max [a])
instance Semilattice (Max a) => Idempotent (Max [a])
instance Semilattice (Max a) => Commutative (Max [a])
instance (Ord' a, Semilattice (Max a)) => Semilattice (Max [a])
instance Semilattice (Max a) => Nil (Max [a]) where nil = Max []
instance Semilattice (Max a) => Monoid (Max [a])

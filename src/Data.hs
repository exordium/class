{-# language UndecidableInstances #-}
{-# language MagicHash #-}
{-# language TypeSynonymInstances #-}
{-# language UndecidableSuperClasses #-}
module Data where
import Types
import Data.Maybe as P
import qualified Prelude as P hiding ((.))
import qualified Numeric.Natural as P
import Fun

data family (#) (c :: * -> Constraint) :: * -> *

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

class Ord' a => Ord a where ord :: a -> a -> Ordering

-- | prop> a . a = a
class Semigroup a => Idempotent a
-- | prop> a . b = b . a
class Semigroup a => Commutative a


newtype Op a = Op a
  deriving newtype (Eq')
  deriving stock (P.Show)
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


class Ord' a => Meet a where (/\) :: a -> a -> a
class Ord' a => Join a where (\/) :: a -> a -> a
class Meet a => Top a where top :: a
class Join a => Bot a where bot :: a

newtype instance Meet # a = Meet a deriving newtype (Meet, Ord',Eq')
instance Meet a => Semigroup (Meet # a) where (.) = (/\)

-- |Absorption: a \/ (a /\ b) == a /\ (a \/ b) == a
-- Implies: top \/ a = top, bottom /\ a = bottom
class (Semilattice a, Semilattice (Op a)) => Lattice a
-- | top /\ a = a
{-class Meet a => Top a where top :: a-}
-- | bottom \/ = a
{-class Join a => Bottom a where bottom :: a-}

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
  (.) :: a -> a -> a
  scale1 :: P.Natural -> a -> a
  scale1 n = scale1# (n P.+ 1) 
instance {-# overlappable #-} Semigroup a => Act a a where act = (.)

class Semigroup a => Act a s where act :: a -> s -> s
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
instance Rg r => Semigroup (Mul r) where Mul a . Mul b = Mul (scale a b)


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


{--- * Instances-}
instance Semigroup () where _ . _ = ()
instance Act    () () where _ `act` _ = ()
instance Nil       () where nil = ()
instance Monoid    ()
deriving via Stock # () instance Eq ()
deriving via Stock # () instance Eq' ()
deriving via Stock # () instance Ord' ()
deriving via Stock # () instance Ord ()
deriving via Stock # () instance Meet ()
deriving via Stock # () instance Join ()
deriving via Stock # () instance Top ()
deriving via Stock # () instance Bot ()

instance Semigroup [x] where (.) = coerce ((P.++) @x)
instance Act [x] [x]  where act = (P.++)
instance Nil [x]     where nil = []
{-instance Monoid (Add [x])-}
instance Semigroup a => Scale [a] [a] where
  scale as bs = [ a . b | a <- as, b <- bs]
instance Semigroup a  => Rg [a]
{-instance Act a s => Act  (Mul [a]) (Mul [s]) where-}
  {-act (Mul as) (Mul bs) = Mul [a `act` b | a <- as, b <- bs]-}
{-instance Nil a => Nil (Mul [a]) where nil = Mul [nil]-}
{-deriving via Stock # [Stock # a] instance Ord a =>  [a]-}




newtype instance Stock # a = Stock0 a
instance P.Eq a => Eq (Stock # a)
instance P.Eq a => Eq' (Stock # a) where
  eq = coerce ((P.==) @a)
  ne = coerce ((P./=) @a)
  comparable _ _ = True

instance P.Ord a => Meet (Stock # a) where (/\) = coerce (P.max @a)
instance P.Ord a => Join (Stock # a) where (\/) = coerce (P.min @a)
instance (P.Ord a, P.Bounded a) => Top (Stock # a) where top = coerce (P.maxBound @a)
instance (P.Ord a, P.Bounded a) => Bot (Stock # a) where bot = coerce (P.minBound @a)

instance P.Ord a => Ord' (Stock # a) where
  (<=) = coerce ((P.<=) @a)
  (<!) = coerce ((P.<) @a)
  (>=) = coerce ((P.>=) @a)
  (>!) = coerce ((P.>) @a)
  ord' (Stock0 a) (Stock0 b) = P.Just (P.compare a b)
instance P.Ord a => Ord (Stock # a) where ord = coerce (P.compare @a)

newtype instance Ord' # a = Ord' a deriving newtype Ord'
instance Ord' a => Eq' (Ord' # a) where
  eq' a b = case ord' a b of 
    Nothing -> Nothing
    Just EQ -> Just True
    _       -> Just False

newtype instance Ord # a = Ord a
  deriving newtype Ord
  deriving anyclass Eq
  deriving Eq' via Ord' # a
instance Ord a => Ord' (Ord # a) where ord' a b = Just (ord a b)

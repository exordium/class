{-# language UndecidableInstances #-}
{-# language TypeSynonymInstances #-}
{-# language MagicHash #-}
{-# language TypeSynonymInstances #-}
{-# language UndecidableSuperClasses #-}
module Data where
import Types
import Data.Maybe as P
import qualified Prelude as P hiding ((.))
import qualified Numeric.Natural as P
import qualified Data.Set as PS
import Fun
import qualified Data.Bits as P

data family (#) (c :: * -> Constraint) :: * -> *
data family (##) (c :: (* -> *) -> Constraint) :: (* -> *) -> * -> *
data family (###) (c :: (* -> * -> *) -> Constraint) :: (* -> * -> *) -> * -> * -> *
infixr #, ##, ###

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
newtype instance Eq # a = Eq a deriving newtype (Eq', Eq)
instance Eq a => P.Eq (Eq # a) where
  (==) = coerce (eq @a)
  (/=) = coerce (ne @a)

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

-- * ord operators in prefix position
leq' a = (<=? a)
leq a = (<= a)
le a = (<! a)
ge a = (>! a)
geq' a = (>=? a)
geq a = (>= a)

instance Eq' a => Eq' [a] where
  eq' [] [] = Just True
  eq' (x:xs) (y:ys) | eq x y = eq' xs ys
  eq' _ _ = Just False

class (Ord' a, Eq a) => Ord a where ord :: a -> a -> Ordering

 -- | prop> a . a = a
class Op a => Idempotent a
-- | prop> a . b = b . a
class Op a => Commutative a

newtype Dual a = Dual a
  deriving newtype (Eq')
  deriving stock (P.Show)
instance Ord' a => Ord' (Dual a) where
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
instance Join a => Meet (Dual a) where (/\) = coerce ((\/) @a)
instance Meet a => Join (Dual a) where (\/) = coerce ((/\) @a)
instance Top a => Bot (Dual a) where bot = Dual top
instance Bot a => Top (Dual a) where top = Dual bot

class Ord' a => Meet a where (/\) :: a -> a -> a
meet a = (/\ a)
class Ord' a => Join a where (\/) :: a -> a -> a
join a = (\/ a)
-- |Absorption: a \/ (a /\ b) == a /\ (a \/ b) == a
-- Implies: top \/ a = top, bottom /\ a = bottom
-- | top /\ a = a
class Meet a => Top a where top :: a
-- | bot \/ = a
class Join a => Bot a where bot :: a

class (Meet & Join) a => Lattice a

newtype instance Meet # a = Meet a deriving newtype (Meet, Ord',Eq')
instance Meet a => Op (Meet # a) where (.) = (/\)
instance Meet a => Idempotent (Meet # a)
instance Meet a => Commutative (Meet # a)

newtype instance Join # a = Join a
  deriving newtype (Join, Ord',Eq')
instance Join a => Op (Join # a) where (.) = coerce ((\/) @a)
instance Join a => Idempotent (Join # a)
instance Join a => Commutative (Join # a)
instance Bot a => Nil (Join # a) where nil = Join bot
instance Bot a => Monoid (Join # a)

instance (Top a, Bot a) => Rg (Join # a) where (*) = coerce ((/\) @a)


class Act a a => Op a where
  (.) :: a -> a -> a
  scale1 :: P.Natural -> a -> a
  scale1 n = scale1# (n P.+ 1) 
instance {-# overlappable #-} Op a => Act a a where act = (.)
op :: Op a => a -> a -> a
op a = (. a)

class Op a => Act a s where act :: a -> s -> s
class Nil a where nil :: a
-- | Decidable 'Nil'. @nil' nil = True@ and otherwise `False`
class Nil a => Nil' a where nil' :: a -> Bool
instance {-# overlappable #-} (Nil a,Eq a) => Nil' a where nil' = eq nil
class (Op a, Nil a) => Monoid a where
  scale0 :: P.Natural -> a -> a
  scale0 0 = \_ -> nil
  scale0 n = scale1# n

-- | inv < inv = id
class Monoid a => Inv a where
  {-# minimal inv #-}
  inv :: a -> a
  inv = (nil -)
  (-) :: a -> a -> a
  a - b = inv b . a
  scalei :: P.Integer -> a -> a
  scalei n a = case P.compare n 0 of
    EQ -> nil
    LT -> scale1# (P.fromInteger (P.abs n)) (inv a)
    GT -> scale1# (P.fromInteger n) a

(+) :: Inv a => a -> a -> a
(+) = (.)

-- | A (right) Near Semiring, Ie a "Ring" without the identity, negation, or commutivity
--(a+b)c = ac + bc
 {-a*(b*c) = (a*b)*c-}
 {-(a.b)*c = a*c . b*c-}
class Monoid r => Rg r where (*) :: r -> r -> r
newtype instance Rg # r = Rg r
instance Rg r => Op (Rg # r) where Rg a . Rg b = Rg (a * b)

one :: forall a. Monoid (Rg # a) => a
one = coerce (nil @(Rg # a))

class (Rg r, Monoid (Rg # r)) => Star r where
  star :: r -> r
  star r = one . (r * star r)


-- | A "Rig": Ring without negatives
class (Rg r, Monoid r, Monoid (Rg # r)) => FromNatural r where
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

 {-| A near semiring (left)module-}
 {-(r*s)a = r(sa)-}
 {-r(as) = (ra)s-}
 {-(r.s)a = ra . sa-}
 {-r(a.b) = ra . rb-}
class (Rg r, Op a) => Scale r a | a -> r where scale :: r -> a -> a

{-instance Rg s => Scale s (a -> s) where scale s f = \a -> f a * s-}
{-instance Op s => Op (a -> s) where f . g = \a -> f a . g a-}
{-instance Monoid s => Nil (a -> s) where nil = \_ -> nil-}
{-instance Monoid s => Monoid (a -> s)-}
{-instance Rg s => Rg (a -> s) where f * g = \a -> f a * g a-}

{-single :: (Eq a, Commutative a, Nil b) => a -> b -> (a -> b)-}
single a = \a' -> if a `eq` a' then one else nil
{-instance (Rg b, Monoid (Rg # b), Monoid a, Nil' a) => Nil (Rg # (a -> b)) where-}
  {-nil = Rg \ a -> if nil' a then one else nil-}
{-instance (Rg b, Monoid (Rg # b), Monoid a, Nil' a) => Monoid (Rg # (a -> b))-}
(|->) :: (Eq a, Monoid b) => a -> b -> a -> b
a |-> b = \a' -> if eq a a' then b else nil



-- | Representational equality


{--- * Instances-}

{-instance Act a s => Act  (Rg # [a]) (Rg # [s]) where-}
  {-act (Rg # as) (Rg # bs) = Rg # [a `act` b | a <- as, b <- bs]-}
{-instance Nil a => Nil (Rg # [a]) where nil = Rg # [nil]-}
{-deriving via Stock # [Stock # a] instance Ord a =>  [a]-}


type Eq# = P.Eq
type Ord# = P.Ord
type Num# = P.Num
type Bounded# = P.Bounded
type Monoid# = P.Monoid
type Op# = P.Semigroup

newtype instance Op# # a = Op# a
instance Op# a => Op (Op# # a) where (.) = coerce ((P.<>) @a)
newtype instance Monoid# # a = Monoid# a deriving Op via Op# # a
instance Monoid# a => Nil (Monoid# # a) where nil = Monoid# P.mempty
instance Monoid# a => Monoid (Monoid# # a)

newtype instance Eq# # a = Eq# a

instance Eq# a => Eq (Eq# # a)
instance Eq# a => Eq' (Eq# # a) where
  eq = coerce ((P.==) @a)
  ne = coerce ((P./=) @a)
  comparable _ _ = True

instance Ord# a => Meet (Ord# # a) where (/\) = coerce (P.min @a)
instance Ord# a => Join (Ord# # a) where (\/) = coerce (P.max @a)

newtype instance Bounded# # a = Bounded# a
  deriving (Eq',Eq,Ord,Ord',Meet,Join) via Ord# # a
instance (Ord# a, Bounded# a) => Top (Bounded# # a) where top = coerce (P.maxBound @a)
instance (Ord# a, Bounded# a) => Bot (Bounded# # a) where bot = coerce (P.minBound @a)

newtype instance Num# # a = Num# a
instance Num# a => Op (Num# # a) where (.) = coerce ((P.+) @a)
instance Num# a => Nil (Num# # a) where nil = Num# $ P.fromInteger 0
instance Num# a => Monoid (Num# # a)
instance Num# a => Nil (Rg # Num# # a) where nil = Rg < Num# $ P.fromInteger 1
instance Num# a => Monoid (Rg # Num# # a)
instance Num# a => Rg (Num# # a) where (*) = coerce ((P.*) @a)

newtype instance Ord# # a = Ord# a
  deriving (Eq',Eq) via Eq# # a

instance Ord# a => Ord' (Ord# # a) where
  (<=) = coerce ((P.<=) @a)
  (<!) = coerce ((P.<) @a)
  (>=) = coerce ((P.>=) @a)
  (>!) = coerce ((P.>) @a)
  ord' (Ord# a) (Ord# b) = P.Just (P.compare a b)
instance Ord# a => Ord (Ord# # a) where ord = coerce (P.compare @a)

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
  deriving P.Eq via (Eq # a)
instance Ord a => Ord' (Ord # a) where ord' a b = Just (ord a b)
instance Ord a => P.Ord (Ord # a) where compare = ord; (<=) = (<=)

-- * Instances
deriving via Num# # Int instance Op Int
deriving via Num# # Int instance Nil Int
deriving via Num# # Int instance Monoid Int
deriving via Num# # Int instance Rg Int
deriving via Rg # Num# # Int instance Nil (Rg # Int)
deriving via Rg # Num# # Int instance Monoid (Rg # Int)
deriving via Bounded# # Int instance Eq' Int
deriving via Bounded# # Int instance Eq Int
deriving via Bounded# # Int instance Ord' Int
deriving via Bounded# # Int instance Ord Int
deriving via Bounded# # Int instance Meet Int
deriving via Bounded# # Int instance Join Int
deriving via Bounded# # Int instance Top Int
deriving via Bounded# # Int instance Bot Int

deriving via Bounded# # Bool instance Eq' Bool
deriving via Bounded# # Bool instance Eq Bool
deriving via Bounded# # Bool instance Ord' Bool
deriving via Bounded# # Bool instance Ord Bool
deriving via Bounded# # Bool instance Meet Bool
deriving via Bounded# # Bool instance Join Bool
instance Op Bool where (.) = P.xor
instance Nil Bool where nil = False
instance Monoid Bool
instance Rg Bool where (*) = (P.&&)

instance Ord a => Scale Bool (PS.Set a) where scale b s = if b then s else PS.empty
instance Ord a => Op (PS.Set a) where
  as' . bs' = coerce# (PS.union as bs `PS.difference` PS.intersection as bs)
    where
      as = coerce# as' :: PS.Set (Ord # a)
      bs = coerce# bs'
instance Ord a => Rg   (PS.Set a) where (*)  = (/\)
instance Ord a => Meet (PS.Set a) where (/\) = coerce# (PS.intersection @(Ord # a))
instance Ord a => Join (PS.Set a) where (\/) = coerce# (PS.union        @(Ord # a))
instance Ord a => Ord' (PS.Set a) where (<=) = coerce# ((P.<=) @(PS.Set  (Ord # a)))
instance Nil (PS.Set a) where nil = PS.empty
instance Ord a => Monoid (PS.Set a)
instance Eq a => Eq (PS.Set a)
instance Eq a => Eq' (PS.Set a) where
  eq = coerce# ((P.==) @(PS.Set (Eq # a)))
  comparable _ _ = True

deriving via Monoid# # () instance Op ()
deriving via Monoid# # () instance Nil ()
deriving via Monoid# # () instance Monoid ()
deriving via Bounded# # () instance Eq ()
deriving via Bounded# # () instance Eq' ()
deriving via Bounded# # () instance Ord' ()
deriving via Bounded# # () instance Ord ()
deriving via Bounded# # () instance Meet ()
deriving via Bounded# # () instance Join ()
deriving via Bounded# # () instance Top ()
deriving via Bounded# # () instance Bot ()

newtype Church a = Church ((a -> a) -> (a -> a))
instance Nil (Church a) where nil = Church \_ -> id
instance Op (Church a) where Church f . Church g = Church \ aa -> f aa > g aa
instance Monoid (Church a)
instance Nil (Rg # Church a) where nil = Rg $ Church id
instance Rg (Church a) where Church f * Church g = Church $ f > g


newtype Endo a = Endo (a -> a)
instance Op (Endo a) where Endo f . Endo g = Endo $ f > g
instance Nil (Endo a) where nil = Endo id
instance Monoid (Endo a)
{-instance Op a => Rg (Endo a) where Endo f * Endo g = Endo \ a -> f a . g a-}
{-instance Monoid a => Nil (Rg # Endo a) where nil = Rg $ Endo \_ -> nil-}

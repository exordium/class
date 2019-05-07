{-# language UndecidableInstances #-}
{-# language TypeSynonymInstances #-}
{-# language MagicHash #-}
{-# language TypeSynonymInstances #-}
{-# language UndecidableSuperClasses #-}
module Data where
import Types
import Data.Maybe as P
import Type.X
import qualified Prelude as P hiding ((.))
import qualified Numeric.Natural as P
import Fun
import qualified Data.Bits as P

import Types.Numeric

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
(==?) :: Eq' a => a -> a -> P.Maybe Bool
a ==? b = eq' b a

-- | comparable = True
--   eq' a b = P.Just (eq a b)
class Eq' a => Eq a
(==), (!=):: Eq a => a -> a -> Bool
a == b = eq b a
a != b = ne b a
infix 4 ==, !=, <!, >!, <?, >?, <=?, >=?, ==#, !=#

newtype instance Eq # a = Eq a deriving newtype (Eq', Eq)
--instance Eq a => P.Eq (Eq # a) where
  --(==) = coerce (eq @a)
  --(/=) = coerce (ne @a)

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
instance Join a => Meet (Dual a) where meet = coerce (join @a)
instance Meet a => Join (Dual a) where join = coerce (meet @a)
instance Top a => Bot (Dual a) where bot = Dual top
instance Bot a => Top (Dual a) where top = Dual bot

class Ord' a => Meet a where meet :: a -> a -> a
class Ord' a => Join a where join :: a -> a -> a

-- |Absorption: a \/ (a /\ b) == a /\ (a \/ b) == a
-- Implies: top \/ a = top, bottom /\ a = bottom
-- | top /\ a = a
class Meet a => Top a where top :: a
-- | bot \/ = a
class Join a => Bot a where bot :: a

class (Meet a, Join a) => Lattice a

newtype instance Meet # a = Meet a deriving newtype (Meet, Ord',Eq')
instance Meet a => Op (Meet # a) where op = meet

newtype instance Join # a = Join a
  deriving newtype (Join, Ord',Eq')
instance Join a => Op (Join # a) where op = coerce (join @a)
instance Bot a => Nil (Join # a) where nil = Join bot
instance Bot a => Scale0 (Join # a)

instance (Top a, Bot a) => Mul (Join # a) where mul = coerce (meet @a) -- TODO: fix


class Op a where
  op :: a -> (a -> a)
  scale1 :: U -> a -> a
  scale1 n = scale1# (n P.+ 1) 
(.) :: Op a => a -> a -> a
a . b = op b a

class Nil a where nil :: a
class (Op a, Nil a) => Scale0 a where
  scale0 :: U -> a -> a
  scale0 0 = \_ -> nil
  scale0 n = scale1# n

class Scale0 m => Prefix m where
  {-# minimal (\\?) | (\\), prefix' #-}
  (\\?) :: m -> m -> Maybe m
  a \\? b = prefix' a b ? Nothing $ Just (a \\ b)
  (\\) :: m -> m -> m
  a \\ b = a \\? b ? b $ id
  prefix' :: m -> m -> Bool
  prefix' m m' = case m \\? m' of {Nothing -> False; Just{} -> True}
class Scale0 m => Suffix m where
  {-# minimal (//?) | (//), suffix' #-}
  (//?)   :: m -> m -> Maybe m
  (//?) a b = suffix' a b ? Nothing $ Just (a // b)
  (//)   :: m -> m -> m
  a // b = a //? b ? b $ id
  suffix' :: m -> m -> Bool
  suffix' m m' = case m //? m' of {Nothing -> False; Just{} -> True}

-- | neg < neg = id
class (Prefix a,Suffix a) => Neg a where
  {-# minimal neg #-}
  neg :: a -> a
  scalei :: I -> a -> a
  scalei n a = case P.compare n 0 of
    EQ -> nil
    LT -> scale1# (P.fromInteger (P.abs n)) (neg a)
    GT -> scale1# (P.fromInteger n) a
--class Op a => Commutative 
--(-) :: (Commutative a, Neg a) => a -> a -> a
--(-) = (//)

newtype instance Neg # a = Neg a
  deriving newtype (Op,Nil,Scale0,Neg)
instance Neg a => Prefix (Neg # a) where
  Neg a \\ Neg b = Neg $ neg a . b
  prefix' _ _ = True
instance Neg a => Suffix (Neg # a) where
  Neg a // Neg b = Neg $ a . neg b
  suffix' _ _ = True

-- | A (right) Near Semiring, Ie a "Ring" without the identity, negation, or commutivity
--(a+b)c = ac + bc
 {-a*(b*c) = (a*b)*c-}
 {-(a.b)*c = a*c . b*c-}
class Op a => Mul a where mul :: a -> a -> a
class Mul a => Mul1 a where one :: a
class Mul1 a => Mul_ a where
  {-# minimal recip #-}
  recip :: a -> a
  recip = (`div` one)
  div :: a -> a -> a
  div = mul < recip
  powi :: I -> a -> a
  powi n a = case P.compare n 0 of
    EQ -> one
    --LT -> scale1# (P.fromInteger (P.abs n)) (Mul $ recip a)
    --GT -> scale1# (P.fromInteger n) a
    

 
class (Scale0 r, Mul1 r) => FromNatural r where
  fromNatural :: U -> r
  fromNatural = (`scale0` one)

--class (FromNatural r, Op_ r, Rg (Dual r)) => Ring r where
  -- | A ring homomorphism from integers
  --
  -- prop> fromInteger (a + b) - fromInteger a + fromInteger b
  -- prop> fromInteger (a * b) - fromInteger a * fromInteger b
  -- prop> fromInteger 0 == nil
  -- prop> fromInteger 1 == one
  -- prop> fromInteger (-x) == neg x
  --fromInteger :: P.Integer -> r
  --fromInteger = (`scalei` one)

--newtype instance Rg # r = Rg r
--instance Rg r => Op (Rg # r) where Rg a `op` Rg b = Rg (b * a)

--newtype instance Ring # r 
--instance (Rg r, Scale0 (Rg # r), Op_ r) => P.Num (Rg # r) where
  --(+) = coerce ((.) @r)
  --(*) = coerce ((*) @r)
  --(-) = coerce ((-) @r)
  --fromInteger = coerce (fromInteger @r)
--deriving via Rg # ((a -> a) -> (a -> a)) instance P.Num ((a -> a) -> (a -> a)) 



-- | Scale by a non-nil @Natural@, this is not checked and will loop on 0.
scale1# :: Op a => U -> a -> a
scale1# y0 x0 = f x0 y0 where
  f x y 
    | P.even y = f (op x x) (y `P.quot` 2)
    | y P.== 1 = x
    | P.otherwise = g (op x x) ((y P.- 1) `P.quot` 2) x
  g x y z 
    | P.even y = g (op x x) (y `P.quot` 2) z
    | y P.== 1 = op z x
    | P.otherwise = g (op x x) ((y P.- 1) `P.quot` 2) (op z x)

{-instance Op s => Op (a -> s) where f . g = \a -> f a . g a-}
{-instance Scale0 s => Nil (a -> s) where nil = \_ -> nil-}
{-instance Scale0 s => Scale0 (a -> s)-}
{-instance Rg s => Rg (a -> s) where f * g = \a -> f a * g a-}

{-single :: (Eq a, Commutative a, Nil b) => a -> b -> (a -> b)-}
single a = \a' -> if a `eq` a' then one else nil
{-instance (Rg b, Scale0 (Rg # b), Scale0 a, Nil' a) => Nil (Rg # (a -> b)) where-}
  {-nil = Rg \ a -> if nil' a then one else nil-}
{-instance (Rg b, Scale0 (Rg # b), Scale0 a, Nil' a) => Scale0 (Rg # (a -> b))-}
(|->) :: (Eq a, Scale0 b) => a -> b -> a -> b
a |-> b = \a' -> if eq a a' then b else nil



-- | Representational equality


{--- * Instances-}

{-instance Act a s => Act  (Rg # [a]) (Rg # [s]) where-}
  {-act (Rg # as) (Rg # bs) = Rg # [a `act` b | a <- as, b <- bs]-}
{-instance Nil a => Nil (Rg # [a]) where nil = Rg # [nil]-}
{-deriving via Stock # [Stock # a] instance Ord a =>  [a]-}


-- | Structural equality.
-- Structually equal values cannot be distinguished by any means.
-- Instances should be stock derived rather than written by hand.
--
type Eq# = P.Eq
(==#) :: (Eq# a, Eq# b, a =# b) => a -> b -> Bool
a ==# b = a P.== coerce b
(!=#) :: (Eq# a, Eq# b, a =# b) => a -> b -> Bool
a !=# b = a P./= coerce b

-- | Structural total ordering.
type Ord# = P.Ord
(<!#), (>!#), (<=#), (>=#) :: (Ord# a, Ord# b, a =# b) => a -> b -> Bool
a <!# b = a P.< coerce b
a >!# b = a P.> coerce b
a <=# b = a P.<= coerce b
a >=# b = a P.>= coerce b

-- | Stock Num class.
type Num# = P.Num
type Bounded# = P.Bounded

type Scale0# = P.Monoid
type Op# = P.Semigroup

newtype instance Op# # a = Op# a
instance Op# a => Op (Op# # a) where Op# a `op` Op# b = Op# (b P.<> a)
newtype instance Scale0# # a = Scale0# a deriving Op via Op# # a
instance Scale0# a => Nil (Scale0# # a) where nil = Scale0# P.mempty
instance Scale0# a => Scale0 (Scale0# # a)

newtype instance Eq# # a = Eq# a

instance Eq# a => Eq (Eq# # a)
instance Eq# a => Eq' (Eq# # a) where
  eq = coerce ((P.==) @a)
  ne = coerce ((P./=) @a)
  comparable _ _ = True

instance Ord# a => Meet (Ord# # a) where meet = coerce (P.min @a)
instance Ord# a => Join (Ord# # a) where join = coerce (P.max @a)

newtype instance Bounded# # a = Bounded# a
  deriving (Eq',Eq,Ord,Ord',Meet,Join) via Ord# # a
instance (Ord# a, Bounded# a) => Top (Bounded# # a) where top = coerce (P.maxBound @a)
instance (Ord# a, Bounded# a) => Bot (Bounded# # a) where bot = coerce (P.minBound @a)

newtype instance Num# # a = Num# a
instance Num# a => Op (Num# # a) where Num# a `op` Num# b = Num# (b P.+ a)
instance Num# a => Nil (Num# # a) where nil = Num# $ P.fromInteger 0
instance Num# a => Scale0 (Num# # a)
instance Num# a => Mul1 (Num# # a) where one = Num# $ P.fromInteger 1
instance Num# a => Mul (Num# # a) where Num# a `mul` Num# b = Num# (b P.* a)
instance Num# a => Neg (Num# # a) where neg = coerce (P.negate @a)
deriving via Neg # Num# # a instance Num# a => Prefix (Num# # a)
deriving via Neg # Num# # a instance Num# a => Suffix (Num# # a)

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
instance Ord a => Ord' (Ord # a) where ord' a b = Just (ord a b)

-- * Instances
deriving via Num# # I64 instance Op I64
deriving via Num# # I64 instance Nil I64
deriving via Num# # I64 instance Scale0 I64
deriving via Num# # I64 instance Mul I64
deriving via Num# # I64 instance Mul1 I64
deriving via Bounded# # I64 instance Eq' I64
deriving via Bounded# # I64 instance Eq I64
deriving via Bounded# # I64 instance Ord' I64
deriving via Bounded# # I64 instance Ord I64
deriving via Bounded# # I64 instance Meet I64
deriving via Bounded# # I64 instance Join I64
deriving via Bounded# # I64 instance Top I64
deriving via Bounded# # I64 instance Bot I64

deriving via Bounded# # Bool instance Eq' Bool
deriving via Bounded# # Bool instance Eq Bool
deriving via Bounded# # Bool instance Ord' Bool
deriving via Bounded# # Bool instance Ord Bool
deriving via Bounded# # Bool instance Meet Bool
deriving via Bounded# # Bool instance Join Bool
instance Op Bool where op = P.xor
instance Nil Bool where nil = False
instance Scale0 Bool
instance Mul Bool where mul = (P.&&)

instance Op () where op () () = ()
instance Nil () where nil = ()
instance Scale0 ()
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
instance Op (Church a) where Church f `op` Church g = Church \ aa -> f aa < g aa
instance Scale0 (Church a)
instance Mul1 (Church a) where one = Church id
instance Mul (Church a) where Church f `mul` Church g = Church $ f < g

instance Nil ((a -> a) -> (a -> a)) where nil = \_ -> id
instance Op ((a -> a) -> (a -> a)) where f `op` g = \aa -> f aa < g aa
instance Scale0 ((a -> a) -> (a -> a))
instance Mul ((a -> a) -> (a -> a)) where mul = (<)
instance Mul1 ((a -> a) -> (a -> a)) where one = id

newtype Endo a = Endo (a -> a)
instance Op (Endo a) where Endo f `op` Endo g = Endo $ f < g
instance Nil (Endo a) where nil = Endo id
instance Scale0 (Endo a)
{-instance Op a => Rg (Endo a) where Endo f * Endo g = Endo \ a -> f a . g a-}
{-instance Scale0 a => Nil (Rg # Endo a) where nil = Rg $ Endo \_ -> nil-}

instance Op X where op = absurd

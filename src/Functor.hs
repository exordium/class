{-# language UndecidableInstances, UndecidableSuperClasses #-}
{-# language MagicHash #-}
module Functor where
import qualified Data.Coerce as GHC
import Data
import Type.I
import Type.O
import Type.K
import Type.E
import Type.X
import qualified Prelude as P
import Types
import Fun
{-import {-# source #-} Control-}

-- | A @FZero f@ is a functor with a particular empty shape singled out
-- Dual to 'Pure'
class (Remap f, Zero (f X)) => FZero f where
  fzero :: f X
  fzero = lose (\x -> x)
  lose :: (a -> X) -> f a
  lose f = remap f absurd fzero
-- | Covariant 'FZero' can be 'empty' for any type.
class (Map f, FZero f, forall x. Zero (f x)) => Empty f where
  empty :: f a
  empty = map absurd fzero

-- | A functor over a particular kliesli category
class (Map f, Monad m) => MapM m f where
  mapM :: (a -> m b) -> f a -> f b
  join :: f (m a) -> f a
  join = mapM \ x -> x
mapM_map :: forall f a b. MapM I f => (a -> b) -> f a -> f b
mapM_map = mapM @I @f < coerce
map_mapM :: Map f => (a -> I b) -> f a -> f b
map_mapM = map < coerce

-- | 
-- prop> filter (False!) = (empty!)
-- prop> filter (True!) = id
class (Empty f, MapM Maybe f) => Filter f where
  filter :: (a -> Bool) -> f a -> f a
  filter f = mapM (\a -> case f a of False -> Nothing; True -> Just a)


class (Traverse IsI f, Strong f, MapM I f) => Map f where
  map :: (a -> b) -> f a -> f b
  constMap :: b -> f a -> f b
  constMap b = map \ _ -> b
($@) :: Map f => (a -> b) -> f a -> f b
($@) = map
(!@) :: Map f => b -> f a -> f b
(!@) = constMap

map_traverse :: (I ~ f, Map t) => (a -> f b) -> t a -> f (t b)
map_traverse aib = I< map (unI< aib)

distribute_pure :: Distribute IsEither t => a -> t a
distribute_pure a = __ -- (id ||| absurd) `map` distribute @IsEither (L a)

class (c ==> Map, Map t) => Distribute c t where
  distribute :: c f => f (t a) -> t (f a)
  distribute = collect @c \ x -> x
  zipWithF   :: c f => (f a -> b) -> f (t a) -> t b
  zipWithF fab = \fta -> map fab (distribute @c fta)
  collect :: c f => (a -> t b) -> f a -> t (f b)
  collect f a = zipWithF @c (\x -> x) (map f a)

class Remap f => Strong f where
  {-# minimal strong | strengthen #-}
  strong :: a -> f b -> f (a,b)
  strong = strengthen (\(a,_) -> a) (\(_,b) -> b) (,)
  strengthen :: (c -> a) -> (c -> b) -> (a -> b -> c) -> a -> f b -> f c
  strengthen f g h a fb = remap (\c -> (f c, g c)) (\(x,y) -> h x y) (strong a fb)
  fill :: a -> f () -> f a
  fill = strengthen (\a -> a) (()!) (\a _ -> a)

class Remap f => Comap f where comap :: (b -> a) -> f a -> f b

class (LMap f, forall x. Map (f x)) => Bimap f
  where bimap :: (x -> a) -> (y -> b) -> f x y -> f a b
class LMap f where lmap :: (a -> b) -> f a x -> f b x

-- | Representational Equality on functors
class    (forall a. f a =# g a) => Coercible1 f g
instance (forall a. f a =# g a) => Coercible1 f g
type (#=#) = Coercible1
coerce1 :: forall g f a. f #=# g => f a -> g a
coerce1 = GHC.coerce
--
-- | 'Representational' types. 
class    ((forall a b. a =# b => f a =# f b),Map# f) => Representational f
instance ((forall a b. a =# b => f a =# f b),Map# f) => Representational f
representational :: forall b a f. (a =# b, Representational f) => f a -> f b
{-# INLINE representational #-}
representational = GHC.coerce

-- | 'Phantom' types can ignore their type parameter. Instances are automatically provided by GHC
class    ((forall x y. f x =# f y)) => Phantom f
instance ((forall x y. f x =# f y)) => Phantom f
phantom :: forall b a f. Phantom f => f a -> f b
phantom = GHC.coerce @(f a) @(f b); {-# INLINE phantom #-}

class Map# f where map# :: a =# b => (a -> b) -> f a -> f b
class Map# f => Remap f where remap :: (b -> a) -> (a -> b) -> f a -> f b
remap_map# :: (Remap f, a =# b) => (a -> b) -> f a -> f b
remap_map# f !x = remap coerce f x
coerce_map# :: (Representational f, a =# b) => (a -> b) -> f a -> f b
coerce_map# _ = coerce
(#@) :: (Map# f, a =# b) => (a -> b) -> f a -> f b
(#@) = map#

class Map t => Traverse c t where
  traverse :: c f => (a -> f b) -> t a -> f (t b)
  traverse afb ta = sequence @c (map afb ta)
  sequence :: c f => t (f a) -> f (t a)
  sequence = traverse @c \ x -> x

for :: (Traverse Applicative t,Applicative f) => t a -> (a -> f b) -> f (t b)
for t f = traverse @Applicative f t
(@@) :: (Traverse Applicative t,Applicative f) => t a -> (a -> f b) -> f (t b)
(@@) = for

class Map f => Apply f where ap :: f (a -> b) -> f a -> f b
class (MapM f f, Apply f) => Bind f where bind :: (a -> f b) -> f a -> f b
class (Pure f, Apply f) => Applicative f
class (Applicative f, Bind f) => Monad f 
-- | A @Pure f@ is a pointed functor with a particular inhabited shape singled out
class (Lifting Zero One f, Remap f) => Pure f where
  fone :: f ()
  fone = pure ()
  pure :: a -> f a
  pure a = remap (()!) (a!) fone

pure_distribute :: (Map t, Pure t) => E x (t a) -> t (E x a)
pure_distribute = pure_distribute -- (pure < L) ||| map R

-- * IsI
class (Map f, f ~ I) => IsI f
instance IsI I
-- * IsK
type family KVal t where KVal (K a) = a
class (Map f, f ~ K (KVal f), c (KVal f)) => IsK c f
instance c a => IsK c (K a)
type family LeftF t where LeftF (E a) = a
class (Map f, f ~ E (LeftF f)) => IsEither f
instance IsEither (E a)

instance Monad f => MapM f (K a) where mapM _ = coerce
instance Map (K a) where map _ = coerce
instance Map# (K a) where map# _ = coerce
instance Remap (K a) where remap _ _ = coerce
instance Strong (K a) where strong _ = coerce

instance Map# I  where map# = coerce_map#
instance Remap I  where remap _ f (I a) = I (f a)
instance Strong I where strong x (I a)  = I (x,a)
instance MapM I I where mapM f (I a) = f a
instance Map I    where map f (I a)     = I (f a)
instance Zero a => One (I a) where one = I zero
instance Pure I where pure = I
instance Apply I where ap (I f) (I a) = I (f a)
instance Applicative I
instance Bind I where bind f (I a) = f a
instance Monad I
instance Traverse IsI I    where traverse = map_traverse
instance (c ==> Map, Map I) => Distribute c I
  where distribute (fia :: f (I a)) = I (map# unI fia)

instance Map# ((,) x)  where map# = coerce_map#
instance Remap ((,) x)  where remap _ f (x,a) = (x, f a)
instance Strong ((,) x) where strong y (x,a)  = (x,(y,a))
instance MapM I ((,) x) where mapM = map_mapM
instance Map ((,) x)    where map f (x,a)     = (x, f a)
instance (c ==> Map, Map ((,) x)) => Traverse c ((,) x)
  where traverse f (x,a) = map (x,) (f a)

instance Traverse IsI (K a) where traverse = map_traverse
instance Zero a => One (K a x) where one = K zero
instance Zero a => Pure (K a) where pure _ = K zero
instance Add a => Apply (K a) where ap (K a) (K b) = K (add a b)
instance Add0 a => Applicative (K a)
instance (c ==> Map, Zero a, Map (K a)) => Distribute c (K a)
  where distribute _ = K zero

instance Map# P.IO where map# = coerce_map#
instance Remap P.IO where remap _ = P.fmap
instance Strong P.IO where strong a = P.fmap (a,)
instance MapM I P.IO where mapM = map_mapM
instance Map P.IO where map = P.fmap
instance Traverse IsI P.IO where traverse = map_traverse

instance (MapM I f, MapM I g) => MapM I (O f g)
  where mapM f (O fg) = O (mapM (I < mapM f) fg)
instance (Map f, Map g) => Map (O f g)
  where map f (O fg) = O (map (map f) fg)
instance (Map f, Map g) => Traverse IsI (O f g) where traverse = map_traverse
instance (Remap f, Remap g) => Map# (O f g) where map# = remap_map# -- TODO: fix this
instance (Remap f, Remap g) => Remap (O f g)
  where remap f g (O fg) = O (remap (remap g f) (remap f g) fg)
instance (Map f, Strong g) => Strong (O f g)
  where strong a (O fg) = O (map (strong a) fg)

instance FZero [] where fzero = []
instance Empty []
instance Remap [] where remap _ = P.map
instance Map# [] where map# = coerce_map#
instance Strong [] where strong a = P.map (a,)
instance MapM I [] where mapM = coerce < map @[]
instance Map [] where map = P.map
instance Pure [] where pure a = [a]
instance (c ==> Applicative) => Traverse c [] where
  traverse f = go where
    go = \case
      [] -> pure []
      a : as -> (:) `map` f a `ap` go as
instance Distribute IsEither [] where
  distribute = \case {L x -> [L x]; R ts -> map R ts}
  zipWithF fab = \case
    L x -> [fab (L x)]
    R ta -> map (\a -> fab (R a)) ta
  collect atb = \case
    L x -> [L x]
    R a -> map R (atb a)

instance Map#   ((->) x) where map# = coerce_map#
instance Remap   ((->) x) where remap _ f g = \a ->  f (g a)
instance Strong  ((->) x) where strong x g  = \a -> (x,g a)
instance MapM I ((->) x) where mapM = map_mapM
instance Map     ((->) x) where map f g     = \a ->  f (g a)
instance Traverse IsI ((->) x)    where traverse = map_traverse

instance Map# (E x) where map# = coerce_map#
instance Remap  (E x) where remap _ f = \case {L x -> L x; R a -> R (f a)}
instance Strong (E x) where strong x  = \case {L x -> L x; R a -> R (x,a)}
instance MapM I (E x) where mapM = map_mapM
instance Map    (E x) where map f     = \case {L x -> L x; R a -> R (f a)}
instance Zero x => Zero (E x a) where zero = L zero
instance Zero a => One (E x a) where one = R zero
instance Pure (E x)   where pure = R
instance (forall f. c f => (Pure f, Map f)) => Traverse c (E x) where
  traverse afb = \case {L x -> pure (L x); R a -> map R (afb a)}
instance Distribute IsEither (E x) where
  distribute = \case {L y -> R (L y); R (L x) -> L x; R (R a) -> R (R a)}


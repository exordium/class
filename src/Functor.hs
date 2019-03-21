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

-- | A @FAdd f@ is a functor with a particular empty shape singled out
-- Dual to 'Pure'
{-class (Remap f, Semigroup (Add (f X))) => FAdd f where-}
  {-fzero :: f X-}
  {-fzero = lose (\x -> x)-}
  {-lose :: (a -> X) -> f a-}
  {-lose f = remap f absurd fzero-}
-- | Covariant 'FAdd' can be 'empty' for any type.
{-class (Map f, FAdd f, forall x. Semigroup (Add (f x))) => Empty f where-}
  {-empty :: f a-}
  {-empty = map absurd fzero-}

-- | A functor over a particular kliesli category
class Bind m m => Bind m f where
  bind :: (a -> m b) -> f a -> f b
  join :: f (m a) -> f a
  join = bind \ x -> x

data family Def1 (c :: (* -> *) -> Constraint) (f :: * -> *) :: * -> *
newtype instance Def1 Remap f a = Remap (f a) deriving newtype Remap
instance Remap f => Map# (Def1 Remap f) where map# f !x = remap coerce f x

newtype instance Def1 Map f a = Map (f a) deriving newtype Map
instance Map f => Bind I (Def1 Map f) where bind = map < coerce
instance Map f => Traverse Wrap (Def1 Map f) where traverse = (wrap <) < map < (unwrap<)
instance Map f => Strong (Def1 Map f) where strong a = map (a,)
instance Map f => Remap (Def1 Map f) where remap _ = map
instance Map f => Map# (Def1 Map f) where map# _ !x = map coerce x

newtype instance Def1 Representational f a = Representational (f a)
instance Representational f => Map# (Def1 Representational f) where map# = coerce_map#

newtype instance Def1 Phantom f a = Phantom (f a)

instance Phantom f => Map (Def1 Phantom f) where map _ = coerce
instance Phantom f => Map# (Def1 Phantom f) where map# _ = coerce
instance Phantom f => Remap (Def1 Phantom f) where remap _ _ = coerce
instance Phantom f => Strong (Def1 Phantom f) where strong _ = coerce
instance (Bind m m, Phantom f) => Bind m (Def1 Phantom f) where bind _ = coerce


newtype instance Def1 (Traverse c) t a = Traverse (t a)
  deriving (Map#, Strong, Remap, Bind I) via (Def1 Map t)
{-instance (Map (Def1 (Traverse c) t), c ==> Map#, Traverse c t) => Traverse c (Def1 (Traverse c) t)-}
  {-where traverse f (Traverse t) = map# Traverse (traverse @c f t)-}
{-instance (c ==> Wrap, Traverse c t) => Map (Def1 (Traverse c) t)-}
  {-where map f = unI < traverse @c (I < f) -}
{-instance Traverse Wrap t => Map (Def1 (Traverse Wrap) t) where-}
  {-map f = unI < traverse @Wrap (I < f)-}

newtype instance Def1 Pure f a = Pure (f a)
  deriving newtype (Pure,Map)
  deriving (Remap,Map#,Strong, Bind I) via Def1 Map f

instance Map f => Traverse Wrap (Def1 Pure f) where -- TODO: fix
  traverse = (wrap <) < map < coerce

instance Pure t => Distribute IsEither (Def1 Pure t) where
  distribute = (pure < L) ||| remap (\(R a) -> a) R

-- TODO: fix
f ||| g = \case {L a -> f a; R b -> g b}

newtype instance Def1 Applicative f a = Applicative (f a)
  deriving newtype (Applicative,Pure,Apply)
  deriving (Remap,Map#,Strong,Bind I) via Def1 Map f

instance Applicative f => Map (Def1 Applicative f) where map = ap < pure


-- | 
-- prop> filter (False!) = (empty!)
-- prop> filter (True!) = id
{-class (Empty f, Bind Maybe f) => Filter f where-}
  {-filter :: (a -> Bool) -> f a -> f a-}
  {-filter f = bind (\a -> case f a of False -> Nothing; True -> Just a)-}


class ({- Traverse Wrap f, -} Strong f, Bind I f) => Map f where
  map :: (a -> b) -> f a -> f b
  constMap :: b -> f a -> f b
  constMap b = map \ _ -> b
($@) :: Map f => (a -> b) -> f a -> f b
($@) = map
(!@) :: Map f => b -> f a -> f b
(!@) = constMap

map_traverse :: (I ~ f, Map t) => (a -> f b) -> t a -> f (t b)
map_traverse = (I<) < map < (unI<)

distribute_pure :: Distribute IsEither t => a -> t a
distribute_pure a = (id ||| absurd) `map` distribute @IsEither (L a)

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

class Apply f where ap :: f (a -> b) -> f a -> f b
class (Map f, Pure f, Apply f) => Applicative f
class (Applicative m, Bind m m) => Monad m
-- | A @Pure f@ is a pointed functor with a particular inhabited shape singled out
-- Technically only @Remap@ is necessary, but @Map@ included for convenience
-- to prevent breaking up @Distribute@'s @zipWithF@
-- prop> pure < f = map f < pure
class ({- Lifting Monoid One f, -} Map f) => Pure f where
  {-# minimal pure | fone #-}
  pure :: a -> f a
  pure a = remap (()!) (a!) fone
  fone :: f ()
  fone = pure ()

-- * Wrap
class (Monad f, Representational f, forall x. x =# f x) => Wrap f
instance (Monad f, Representational f, forall x. x =# f x) => Wrap f
wrap :: Wrap f => a -> f a
wrap = coerce
unwrap :: Wrap f => f a -> a
unwrap = coerce
newtype instance Def1 Wrap f a = Wrap (f a)
instance Wrap f => Pure (Def1 Wrap f) where pure = coerce
instance Wrap f => Apply (Def1 Wrap f) where ap fab fa = wrap ((unwrap fab) (unwrap fa))
instance Wrap f => Applicative (Def1 Wrap f)
instance Wrap f => Bind (Def1 Wrap f) (Def1 Wrap f) where bind = coerce
instance Wrap f => Monad (Def1 Wrap f)
instance Wrap f => Map (Def1 Wrap f) where map = coerce
deriving via Def1 Representational f instance Representational f => Map# (Def1 Wrap f)
deriving via Def1 Map f instance Wrap f => Strong (Def1 Wrap f)
deriving via Def1 Map f instance Wrap f => Remap (Def1 Wrap f)
deriving via Def1 Map f instance Wrap f => Bind I (Def1 Wrap f)

newtype instance Def1 (Bind m) f a = Bind (f a)
  deriving newtype (Bind m)
  {-deriving (Bind I, Map#,Remap,Strong) via Def1 Map (Def1 Bind m) -}
{-instance Bind m => Map (Def1 Bind m) where map f (Bind ma) = Bind (map f ma)-}
instance Bind m m => Bind (Def1 (Bind m) m) (Def1 (Bind m) m) where
  bind f (Bind m) = Bind (bind (\(f -> Bind b) -> b) m)
{-instance Bind m => Apply (Def1 Bind m) ap where-}
  {-ap fab fa = bind pure-}

{-newtype instance Def1 Monad m a = Monad (m a)-}
  {-deriving (Bind I, Map#,Remap,Strong) via Def1 Map (Def1 Monad m) -}
  {-deriving (Bind, Map) via Def1 Bind m-}

{-newtype II a = II a-}
  {-deriving (Map,Strong,Remap,Bind I, Map#,Monad) via Def1 Wrap II-}
{-instance Wrap f => Map (Def1 Wrap f) where map = coerce-}
{-class (Map f, f ~ I) => Wrap f-}
{-instance Wrap I-}
-- * IsK
type family KVal t where KVal (K a) = a
class (Map f, f ~ K (KVal f), c (KVal f)) => IsK c f
instance c a => IsK c (K a)
type family LeftF t where LeftF (E a) = a
class (Map f, f ~ E (LeftF f)) => IsEither f
instance IsEither (E a)

deriving via Def1 Phantom (K a) instance Map (K a)
deriving via Def1 Phantom (K a) instance Map# (K a)
deriving via Def1 Phantom (K a) instance Remap (K a)
deriving via Def1 Phantom (K a) instance Strong (K a)
deriving via Def1 Phantom (K a) instance Bind f f => Bind f (K a)

{-instance Traverse Wrap (K a) where traverse = map_traverse-}
instance Semigroup a => Apply (K a) where ap (K a) (K b) = K (a . b)
instance Monoid a => Pure (K a) where pure _ = K nil -- TODO: check this vs one
instance Monoid a => Applicative (K a)
instance (c ==> Map, Monoid a, Map (K a)) => Distribute c (K a)
  where distribute _ = K nil
instance Monoid a => Monad (K a)

deriving via Def1 Wrap I instance Map# I
deriving via Def1 Wrap I instance Remap I
deriving via Def1 Wrap I instance Strong I
deriving via Def1 Wrap I instance (Bind I) I
deriving via Def1 Wrap I instance Map I
deriving via Def1 Wrap I instance Pure I
deriving via Def1 Wrap I instance Apply I
deriving via Def1 Wrap I instance Applicative I
deriving via Def1 Wrap I instance Monad I

deriving newtype instance Semigroup a => Semigroup (I a)
instance Semigroup a => Act (I a) (I a) where act (I a) (I b) = I (act a b)
deriving newtype instance Nil a => Nil (I a)
deriving newtype instance Monoid a => Monoid (I a)
{-instance Traverse Wrap I    where traverse = map_traverse-}
instance (c ==> Map, Map I) => Distribute c I
  where distribute (fia :: f (I a)) = I (map# unI fia)


deriving via Def1 Representational ((,) x) instance Map# ((,) x)
deriving via Def1 Map ((,) x) instance Remap ((,) x)
deriving via Def1 Map ((,) x) instance Strong ((,) x)
deriving via Def1 Map ((,) x) instance Bind I ((,) x)
{-deriving via Def1 (Traverse Map) ((,) x) instance Map ((,) x)-}

instance Map ((,) x)    where map f (x,a)     = (x, f a)
instance (c ==> Map, Map ((,) x)) => Traverse c ((,) x)
  where traverse f (x,a) = map (x,) (f a)


deriving via Def1 Map P.IO instance Bind I P.IO
deriving via Def1 Map P.IO instance Remap P.IO
deriving via Def1 Map P.IO instance Strong P.IO
deriving via Def1 Representational P.IO instance Map# P.IO
instance Map P.IO where map = P.fmap
{-instance Traverse Wrap P.IO where traverse = map_traverse-}

instance (Bind I f, Bind I g) => Bind I (O f g)
  where bind f (O fg) = O (bind (I < bind f) fg)
instance (Map f, Map g) => Map (O f g)
  where map f (O fg) = O (map (map f) fg)
{-instance (Map f, Map g) => Traverse Wrap (O f g) where traverse = map_traverse-}
instance (Remap f, Remap g) => Map# (O f g) where map# = remap_map# -- TODO: fix this
instance (Remap f, Remap g) => Remap (O f g)
  where remap f g (O fg) = O (remap (remap g f) (remap f g) fg)
instance (Map f, Strong g) => Strong (O f g)
  where strong a (O fg) = O (map (strong a) fg)

{-instance FAdd [] where fzero = []-}
{-instance Empty []-}
deriving via Def1 Representational [] instance Map# []
deriving via Def1 Map [] instance Remap []
deriving via Def1 Map [] instance Strong []
deriving via Def1 Map [] instance Bind I []
{-deriving via Def1 (Traverse Wrap) [] instance Map []-}
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

instance Map ((->) x) where map f g = \a ->  f (g a)
deriving via Def1 Representational ((->) x) instance Map# ((->) x)
deriving via Def1 Map ((->) x) instance Remap ((->) x)
deriving via Def1 Map ((->) x) instance Strong ((->) x)
deriving via Def1 Map ((->) x) instance Bind I ((->) x)
{-instance Traverse Wrap ((->) x) where traverse = map_traverse-}

deriving via Def1 Representational (E x) instance Map# (E x)
deriving via Def1 Map (E x) instance Remap (E x)
deriving via Def1 Map (E x) instance Strong (E x)
deriving via Def1 Map (E x) instance Bind I (E x)
instance Map    (E x) where map f     = \case {L x -> L x; R a -> R (f a)}
{-instance Monoid x => FAdd (E x) where-}
  
{-instance Monoid x => Semigroup (Add (E x a)) where nil = L nil-}
{-instance Monoid x => Monoid (Add (E x a)) where nil = L nil-}
{-instance Monoid a => Monoid (Times (E x a)) where one = R nil-}
instance Pure (E x)   where pure = R
instance (forall f. c f => (Pure f, Map f)) => Traverse c (E x) where
  traverse afb = \case {L x -> pure (L x); R a -> map R (afb a)}
instance Distribute IsEither (E x) where
  distribute = \case {L y -> R (L y); R (L x) -> L x; R (R a) -> R (R a)}


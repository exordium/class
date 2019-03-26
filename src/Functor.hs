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
import qualified Data.Set as PS

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

class Bind m where
  bind :: (a -> m b) -> m a -> m b
  join :: m (m a) -> m a
  join = bind \ x -> x

data family (#) (c :: (* -> *) -> Constraint) :: (* -> *) -> * -> *
newtype instance (Remap # f) a = Remap (f a) deriving newtype Remap
instance Remap f => Map# (Remap # f) where map# f !x = remap coerce f x

newtype instance (Map # f) a = Map (f a) deriving newtype Map
instance Map f => Traverse Wrap (Map # f) where traverse = (wrap <) < map < (unwrap<)
instance Map f => Strong (Map # f) where strong a = map (a,)
instance Map f => Remap (Map # f) where remap _ = map
instance Map f => Map# (Map # f) where map# _ !x = map coerce x

newtype instance (Representational # f) a = Representational (f a)
instance Representational f => Map# (Representational # f) where map# _ = coerce

newtype instance (Phantom # f) a = Phantom (f a)

instance Phantom f => Map (Phantom # f) where map _ = coerce
instance Phantom f => Map# (Phantom # f) where map# _ = coerce
instance Phantom f => Remap (Phantom # f) where remap _ _ = coerce
instance Phantom f => Strong (Phantom # f) where strong _ = coerce
instance Phantom f => Bind (Phantom # f) where bind _ = coerce
{-instance (Bind m, Phantom f) => Bind m (Phantom # f) where bind _ = coerce-}


newtype instance (Traverse c # t) a = Traverse (t a)
  deriving (Map#, Strong, Remap) via (Map # t)
{-instance (Map (Def1 (Traverse c) t), c ==> Map#, Traverse c t) => Traverse c (Def1 (Traverse c) t)-}
  {-where traverse f (Traverse t) = map# Traverse (traverse @c f t)-}
{-instance (c ==> Wrap, Traverse c t) => Map (Def1 (Traverse c) t)-}
  {-where map f = unI < traverse @c (I < f) -}
{-instance Traverse Wrap t => Map (Def1 (Traverse Wrap) t) where-}
  {-map f = unI < traverse @Wrap (I < f)-}

newtype instance (Pure # f) a = Pure (f a)
  deriving newtype (Pure,Map)
  deriving (Remap,Map#,Strong) via Map # f

instance Map f => Traverse Wrap (Pure # f) where -- TODO: fix
  traverse = (wrap <) < map < coerce

-- TODO: fix
f ||| g = \case {L a -> f a; R b -> g b}

newtype instance (Applicative # f) a = Applicative (f a)
  deriving newtype (Applicative,Pure,Apply)
  deriving (Remap,Map#,Strong) via Map # f

instance Applicative f => Map (Applicative # f) where map = ap < pure


-- | 
-- prop> filter (False!) = (empty!)
-- prop> filter (True!) = id
{-class (Empty f, Bind Maybe f) => Filter f where-}
  {-filter :: (a -> Bool) -> f a -> f a-}
  {-filter f = bind (\a -> case f a of False -> Nothing; True -> Just a)-}


class ({- Traverse Wrap f, -} Strong f) => Map f where
  map :: (a -> b) -> f a -> f b
  constMap :: b -> f a -> f b
  constMap b = map \ _ -> b
($@) :: Map f => (a -> b) -> f a -> f b
($@) = map
(!@) :: Map f => b -> f a -> f b
(!@) = constMap

map_traverse :: (I ~ f, Map t) => (a -> f b) -> t a -> f (t b)
map_traverse = (I<) < map < (unI<)

class Map t => Distribute t where
  distribute :: Map f => f (t a) -> t (f a)
  distribute = collect \ x -> x
  zipWithF   :: Map f => (f a -> b) -> f (t a) -> t b
  zipWithF fab = \fta -> fab `map` distribute fta
  collect :: Map f => (a -> t b) -> f a -> t (f b)
  collect f a = zipWithF (\x -> x) (map f a)

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
class (Map f, Pure f, Apply f) => Applicative f
class (Applicative m, Bind m) => Monad m
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
newtype instance (Wrap # f) a = Wrap (f a)
instance Wrap f => Pure (Wrap # f) where pure = coerce
instance Wrap f => Apply (Wrap # f) where ap fab fa = wrap ((unwrap fab) (unwrap fa))
instance Wrap f => Applicative (Wrap # f)
instance Wrap f => Bind (Wrap # f) where bind = coerce
instance Wrap f => Monad (Wrap # f)
instance Wrap f => Map (Wrap # f) where map = coerce
deriving via Representational # f instance Representational f => Map# (Wrap # f)
deriving via Map # f instance Wrap f => Strong (Wrap # f)
deriving via Map # f instance Wrap f => Remap (Wrap # f)

newtype instance (Bind # m) a = Bind (m a) 
  {-deriving newtype Bind-}

  {-deriving (Bind I, Map#,Remap,Strong) via Map # (Bind # m) -}
{-instance Bind m => Map (Bind # m) where map f (Bind ma) = Bind (map f ma)-}
instance Bind m => Bind (Bind # m) where
  bind f (Bind m) = Bind (bind (\(f -> Bind b) -> b) m)
{-instance Bind m => Apply (Bind # m) ap where-}
  {-ap fab fa = bind pure-}

{-newtype instance Monad # m a = Monad (m a)-}
  {-deriving (Bind I, Map#,Remap,Strong) via Map # (Monad # m) -}
  {-deriving (Bind, Map) via Bind # m-}

{-newtype II a = II a-}
  {-deriving (Map,Strong,Remap,Bind I, Map#,Monad) via Wrap # II-}
{-instance Wrap f => Map (Wrap # f) where map = coerce-}
{-class (Map f, f ~ I) => Wrap f-}
{-instance Wrap I-}
-- * IsK
type family KVal t where KVal (K a) = a
class (Map f, f ~ K (KVal f), c (KVal f)) => IsK c f
instance c a => IsK c (K a)
type family LeftF t where LeftF (E a) = a
class (Map f, f ~ E (LeftF f)) => IsEither f
instance IsEither (E a)

deriving via Phantom # (K a) instance Map (K a)
deriving via Phantom # (K a) instance Map# (K a)
deriving via Phantom # (K a) instance Remap (K a)
deriving via Phantom # (K a) instance Strong (K a)
deriving via Phantom # (K a) instance Bind (K a)

{-instance Traverse Wrap (K a) where traverse = map_traverse-}
instance Semigroup a => Apply (K a) where ap (K a) (K b) = K (a . b)
instance Monoid a => Pure (K a) where pure _ = K nil -- TODO: check this vs one
instance Monoid a => Applicative (K a)
instance (Monoid a) => Distribute (K a) where distribute _ = K nil
instance Monoid a => Monad (K a)

deriving via Wrap # I instance Map# I
deriving via Wrap # I instance Remap I
deriving via Wrap # I instance Strong I
{-deriving via Wrap # I instance Bind I-}
deriving via Wrap # I instance Map I
deriving via Wrap # I instance Pure I
deriving via Wrap # I instance Apply I
deriving via Wrap # I instance Applicative I
deriving via Wrap # I instance Bind I
deriving via Wrap # I instance Monad I

deriving newtype instance Semigroup a => Semigroup (I a)
instance Semigroup a => Act (I a) (I a) where act (I a) (I b) = I (act a b)
deriving newtype instance Nil a => Nil (I a)
deriving newtype instance Monoid a => Monoid (I a)
{-instance Traverse Wrap I    where traverse = map_traverse-}
instance Distribute I where distribute (fia :: f (I a)) = I (map# unI fia)


deriving via Representational # ((,) x) instance Map# ((,) x)
deriving via Map # ((,) x) instance Remap ((,) x)
deriving via Map # ((,) x) instance Strong ((,) x)
{-deriving via Def1 (Traverse Map) ((,) x) instance Map ((,) x)-}

instance Map ((,) x)    where map f (x,a)     = (x, f a)
instance (c ==> Map, Map ((,) x)) => Traverse c ((,) x)
  where traverse f (x,a) = map (x,) (f a)


deriving via Map # P.IO instance Remap P.IO
deriving via Map # P.IO instance Strong P.IO
deriving via Representational # P.IO instance Map# P.IO
instance Map P.IO where map = P.fmap
{-instance Traverse Wrap P.IO where traverse = map_traverse-}

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
deriving via Representational # [] instance Map# []
deriving via Map # [] instance Remap []
deriving via Map # [] instance Strong []
{-deriving via Def1 (Traverse Wrap) [] instance Map []-}
instance Map [] where map = P.map
instance Pure [] where pure a = [a]
instance (c ==> Applicative) => Traverse c [] where
  traverse f = go where
    go = \case
      [] -> pure []
      a : as -> (:) `map` f a `ap` go as

instance Map ((->) x) where map f g = \a ->  f (g a)
deriving via Representational # ((->) x) instance Map# ((->) x)
deriving via Map # ((->) x) instance Remap ((->) x)
deriving via Map # ((->) x) instance Strong ((->) x)
instance Distribute ((->) x) where distribute fxa = \x -> map ($ x) fxa
{-instance Traverse Wrap ((->) x) where traverse = map_traverse-}

deriving via Representational # (E x) instance Map# (E x)
deriving via Map # (E x) instance Remap (E x)
deriving via Map # (E x) instance Strong (E x)
instance Map    (E x) where map f     = \case {L x -> L x; R a -> R (f a)}
{-instance Monoid x => FAdd (E x) where-}
  
{-instance Monoid x => Semigroup (Add (E x a)) where nil = L nil-}
{-instance Monoid x => Monoid (Add (E x a)) where nil = L nil-}
{-instance Monoid a => Monoid (Times (E x a)) where one = R nil-}
instance Pure (E x)   where pure = R
instance (forall f. c f => (Pure f, Map f)) => Traverse c (E x) where
  traverse afb = \case {L x -> pure (L x); R a -> map R (afb a)}

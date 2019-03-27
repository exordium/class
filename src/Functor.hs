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


data family (#) (c :: (* -> *) -> Constraint) :: (* -> *) -> * -> *
newtype instance (Remap # f) a = Remap (f a) deriving newtype Remap
instance Remap f => Map# (Remap # f) where map# f !x = remap coerce f x

newtype instance (Map # f) a = Map (f a) deriving newtype Map
{-instance Map f => TraverseC Wrap (Map # f) where traverseC = (wrap <) < map < (unwrap<)-}
instance Map f => Remap (Map # f) where remap _ = map
instance Map f => Map# (Map # f) where map# _ !x = map coerce x

newtype instance (Representational # f) a = Representational (f a)
instance Representational f => Map# (Representational # f) where map# _ = coerce

newtype instance (Phantom # f) a = Phantom (f a)

instance Phantom f => Map (Phantom # f) where map _ = coerce
instance Phantom f => Map# (Phantom # f) where map# _ = coerce
instance Phantom f => Remap (Phantom # f) where remap _ _ = coerce
{-instance (Bind m, Phantom f) => Bind m (Phantom # f) where bind _ = coerce-}
phantom_traverseC :: (Phantom t, c ==> Pure, c f) => (a -> f b) -> t a -> f (t b)
phantom_traverseC _ = pure < phantom
-- Doesn't actually work because deriving via can't get under @f@, use above instead
instance (Phantom f, c ==> Pure) => TraverseC c (Phantom # f) where
  traverseC f (Phantom k) = (pure < Phantom < phantom) k

newtype instance (Pure # f) a = Pure (f a)
  deriving newtype (Pure,Map)
  deriving (Remap,Map#) via Map # f

{-instance Map f => TraverseC Wrap (Pure # f) where -- TODO: fix-}
  {-traverseC = (wrap <) < map < coerce-}

-- TODO: fix
f ||| g = \case {L a -> f a; R b -> g b}

newtype instance (Applicative # f) a = Applicative (f a)
  deriving newtype (Applicative,Pure,Apply)
  deriving (Remap,Map#) via Map # f

instance Applicative f => Map (Applicative # f) where map = ap < pure


-- | 
-- prop> filter (False!) = (empty!)
-- prop> filter (True!) = id
{-class (Empty f, Bind Maybe f) => Filter f where-}
  {-filter :: (a -> Bool) -> f a -> f a-}
  {-filter f = bind (\a -> case f a of False -> Nothing; True -> Just a)-}


class Remap f => Map f where
  map :: (a -> b) -> f a -> f b
  constMap :: b -> f a -> f b
  constMap b = map \ _ -> b

($@) :: Map f => (a -> b) -> f a -> f b
($@) = map
(!@) :: Map f => b -> f a -> f b
(!@) = constMap


class Map t => Distribute t where
  distribute :: Map f => f (t a) -> t (f a)
  distribute = collect \ x -> x
  zipWithF   :: Map f => (f a -> b) -> f (t a) -> t b
  zipWithF fab = \fta -> fab `map` distribute fta
  collect :: Map f => (a -> t b) -> f a -> t (f b)
  collect f a = zipWithF (\x -> x) (map f a)


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
class    ((forall x y. f x =# f y)
         ,(forall c. c ==> Pure => TraverseC c f)) => Phantom f
instance ((forall x y. f x =# f y)
         ,(forall c. c ==> Pure => TraverseC c f)) => Phantom f
phantom :: forall b a f. Phantom f => f a -> f b
phantom = GHC.coerce @(f a) @(f b); {-# INLINE phantom #-}

class Map# f where map# :: a =# b => (a -> b) -> f a -> f b
class Map# f => Remap f where remap :: (b -> a) -> (a -> b) -> f a -> f b
remap_map# :: (Remap f, a =# b) => (a -> b) -> f a -> f b
remap_map# f !x = remap coerce f x
(#@) :: (Map# f, a =# b) => (a -> b) -> f a -> f b
(#@) = map#
strong :: Remap f => a -> f b -> f (a,b)
strong a = remap (\(_,b) -> b) (a,)

class ({- forall cc. (cc ==> c) => TraverseC cc t, c ==> Map#, -} Map t) => TraverseC c t where
  traverseC :: c f => (a -> f b) -> t a -> f (t b)
  traverseC afb ta = sequence @c (map afb ta)
  sequence :: c f => t (f a) -> f (t a)
  sequence = traverseC @c \ x -> x

for :: (TraverseC Applicative t,Applicative f) => t a -> (a -> f b) -> f (t b)
for t f = traverseC @Applicative f t

(@@) :: (TraverseC Applicative t,Applicative f) => t a -> (a -> f b) -> f (t b)
(@@) = for

for1 :: (TraverseC Apply t,Apply f) => t a -> (a -> f b) -> f (t b)
for1 t f = traverseC @Apply f t

for0 :: (TraverseC Pure t,Pure f) => t a -> (a -> f b) -> f (t b)
for0 t f = traverseC @Pure f t

for_ :: (TraverseC Map t,Map f) => t a -> (a -> f b) -> f (t b)
for_ t f = traverseC @Map f t



class Map f => Apply f where ap :: f (a -> b) -> f a -> f b
class (Map f, Pure f, Apply f) => Applicative f
class Applicative m => Monad m where bind :: (a -> m b) -> m a -> m b
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

newtype instance (Monad # m) a = Monad (m a)
  deriving newtype (Monad, Applicative, Pure)
  deriving (Map#,Map, Remap) via Map # (Monad # m) 
instance Monad m => Apply (Monad # m) where
  ap (Monad mab) (Monad ma) = Monad ((`bind` mab) \ ab -> (`bind` ma) (pure < (ab $)))
{-instance Monad m => Bind (Monad # m) where -}

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
instance c ==> Pure => TraverseC c (K a) where traverseC _ (K a) = pure (K a)

map_traverseC :: (I ~ f, Map t) => (a -> f b) -> t a -> f (t b)
map_traverseC = (I<) < map < (unI<)
instance Semigroup a => Apply (K a) where ap (K a) (K b) = K (a . b)
instance Monoid a => Pure (K a) where pure _ = K nil -- TODO: check this vs one
instance Monoid a => Applicative (K a)
instance Monoid a => Distribute (K a) where distribute _ = K nil
instance Monoid a => Monad (K a) where bind _ = coerce

instance Pure I where pure = I
instance Apply I where ap = coerce
instance Applicative I
instance Monad I where bind = coerce
instance Map I where map = coerce
deriving via Representational # I instance Map# I
deriving via Map # I instance Remap I
instance c ==> Map# => TraverseC c I where traverseC f (I a) = map# I (f a)

newtype II a = II a deriving (Monad,Applicative,Apply,Pure,Map,Map#,Remap) via I


deriving newtype instance Semigroup a => Semigroup (I a)
instance Semigroup a => Act (I a) (I a) where act (I a) (I b) = I (act a b)
deriving newtype instance Nil a => Nil (I a)
deriving newtype instance Monoid a => Monoid (I a)
{-instance TraverseC Wrap I    where traverseC = map_traverseC-}
instance Distribute I where distribute (fia :: f (I a)) = I (map# unI fia)


deriving via Representational # ((,) x) instance Map# ((,) x)
deriving via Map # ((,) x) instance Remap ((,) x)
instance Map ((,) x) where map f (x,a) = (x, f a)
instance c ==> Remap => TraverseC c ((,) x) 
  where traverseC f (x,a) = remap (\(_,b) -> b) (x,) (f a)

newtype Endo a = Endo (a -> a)
  deriving Map# via Representational # Endo
instance Remap Endo where remap ba ab (Endo aa) = Endo (ba > aa > ab)

deriving via Map # P.IO instance Remap P.IO
deriving via Monad # P.IO instance Map P.IO
{-deriving via Monad # P.IO instance Apply P.IO-}
{-deriving via Monad # P.IO instance Bind P.IO-}
deriving via Representational # P.IO instance Map# P.IO

instance (Map f, Map g) => Map (O f g)
  where map f (O fg) = O (map (map f) fg)
{-instance (Map f, Map g) => TraverseC Wrap (O f g) where traverseC = map_traverseC-}
instance (Remap f, Remap g) => Map# (O f g) where map# = remap_map# -- TODO: fix this
instance (Remap f, Remap g) => Remap (O f g)
  where remap f g (O fg) = O (remap (remap g f) (remap f g) fg)

{-instance FAdd [] where fzero = []-}
{-instance Empty []-}
deriving via Representational # [] instance Map# []
deriving via Map # [] instance Remap []
{-deriving via Def1 (TraverseC Wrap) [] instance Map []-}
instance Map [] where map = P.map
instance Pure [] where pure a = [a]
instance (c ==> Applicative) => TraverseC c [] where
  traverseC f = go where
    go = \case
      [] -> pure []
      a : as -> (:) `map` f a `ap` go as

instance Map ((->) x) where map f g = \a ->  f (g a)
deriving via Representational # ((->) x) instance Map# ((->) x)
deriving via Map # ((->) x) instance Remap ((->) x)
instance Distribute ((->) x) where distribute fxa = \x -> map ($ x) fxa
{-instance TraverseC Wrap ((->) x) where traverseC = map_traverseC-}

deriving via Representational # (E x) instance Map# (E x)
deriving via Map # (E x) instance Remap (E x)
instance Map    (E x) where map f     = \case {L x -> L x; R a -> R (f a)}
{-instance Monoid x => FAdd (E x) where-}
  
{-instance Monoid x => Semigroup (Add (E x a)) where nil = L nil-}
{-instance Monoid x => Monoid (Add (E x a)) where nil = L nil-}
{-instance Monoid a => Monoid (Times (E x a)) where one = R nil-}
instance Pure (E x)   where pure = R
instance (forall f. c f => (Pure f, Map f)) => TraverseC c (E x) where
  traverseC afb = \case {L x -> pure (L x); R a -> map R (afb a)}

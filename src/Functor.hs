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



data family (##) (c :: (* -> *) -> Constraint) :: (* -> *) -> * -> *
infixr ##
newtype instance (Remap ## f) a = Remap (f a) deriving newtype Remap
instance Remap f => Map# (Remap ## f) where map# f !x = remap coerce f x

newtype instance (Map ## f) a = Map (f a) deriving newtype Map
{-instance Map f => TraverseC Wrap (Map ## f) where traverseC = (wrap <) < map < (unwrap<)-}
instance Map f => Remap (Map ## f) where remap _ = map
instance Map f => Map# (Map ## f) where map# _ !x = map coerce x

newtype instance (Representational ## f) a = Representational (f a)
instance Representational f => Map# (Representational ## f) where map# _ = coerce

newtype instance (Phantom ## f) a = Phantom (f a)

instance Phantom f => Map (Phantom ## f) where map _ = coerce
instance Phantom f => Map# (Phantom ## f) where map# _ = coerce
instance Phantom f => Remap (Phantom ## f) where remap _ _ = coerce
{-instance (Bind m, Phantom f) => Bind m (Phantom ## f) where bind _ = coerce-}
phantom_traverseC :: (Phantom t, c ==> Pure, c f) => (a -> f b) -> t a -> f (t b)
phantom_traverseC _ = pure < phantom
-- Doesn't actually work because deriving via can't get under @f@, use above instead
instance (Phantom f, c ==> Pure) => TraverseC c (Phantom ## f) where
  traverseC f (Phantom k) = (pure < Phantom < phantom) k

newtype instance (Pure ## f) a = Pure (f a)
  deriving newtype (Pure,Map)
  deriving (Remap,Map#) via Map ## f

{-instance Map f => TraverseC Wrap (Pure ## f) where -- TODO: fix-}
  {-traverseC = (wrap <) < map < coerce-}

-- TODO: fix
f ||| g = \case {L a -> f a; R b -> g b}

newtype instance (Applicative ## f) a = Applicative (f a)
  deriving newtype (Applicative,Pure,Apply)
  deriving (Monoidal (,)) via Apply ## f
  deriving (Remap,Map#) via Map ## f

instance Applicative f => Map (Applicative ## f) where map = ap < pure

-- | @f@ is a Monad-Module over @m@
class Monad m => Bound m f where bound :: (a -> m b) -> f a -> f b
instance {-# overlappable #-} Monad m => Bound m m where bound = bind
instance Bound Maybe [] where
  bound f = go where
    go [] = []
    go ((f -> Nothing):as)  =     go as
    go ((f -> Just b) :as)  = b : go as

instance Pure Maybe where pure = Just
instance Monad Maybe where bind f = \case {Nothing -> Nothing; Just a -> f a}
deriving via Monad ## Maybe instance Applicative Maybe
deriving via Monad ## Maybe instance Apply Maybe
deriving via Monad ## Maybe instance Monoidal (,) Maybe
deriving via Monad ## Maybe instance Map Maybe
deriving via Monad ## Maybe instance Remap Maybe
deriving via Representational ## Maybe instance Map# Maybe




-- | 
-- prop> filter (False!) = (empty!)
-- prop> filter (True!) = id
class (Empty f, Bound Maybe f) => Filter f where
  filter :: (a -> Bool) -> f a -> f a
  filter f = bound \ a -> case f a of {False -> Nothing; True -> Just a}
instance {-# overlappable #-} (Empty f, Bound Maybe f) => Filter f
instance Filter [] where filter = P.filter


class Remap f => Map f where
  map :: (a -> b) -> f a -> f b
  constMap :: b -> f a -> f b
  constMap b = map \ _ -> b

($@) :: Map f => (a -> b) -> f a -> f b
($@) = map
(!@) :: Map f => b -> f a -> f b
(!@) = constMap
--
-- | Covariant E-monoidal functors can be appended
class (Monoidal E f, Map f) => Append f where
  append :: f a -> f a -> f a
  append fa fa' = map (\case L a -> a; R b -> b) (fa `monoidal` fa')


class Map t => Distribute t where
  distribute :: Map f => f (t a) -> t (f a)
  distribute = collect \ x -> x
  zipWithF   :: Map f => (f a -> b) -> f (t a) -> t b
  zipWithF fab = \fta -> fab `map` distribute fta
  collect :: Map f => (a -> t b) -> f a -> t (f b)
  collect f a = zipWithF (\x -> x) (map f a)


class Remap f => Comap f where comap :: (b -> a) -> f a -> f b

newtype instance (Comap ## f) a = Comap (f a)
  deriving newtype Comap
  deriving Map# via Remap ## f
instance Comap f => Remap (Comap ## f) where remap f _ = comap f

class (Comap f, Monoidal (,) f) => FDivide f where
  fdivide :: (x -> a) -> (x -> b) -> f a -> f b -> f x
  fdivide f g fa fb = comap (\x -> (f x, g x)) (fa `monoidal` fb)

newtype instance (FDivide ## f) a = FDivide (f a)
  deriving newtype (FDivide,Comap)
  deriving (Remap,Map#) via Comap ## f


instance FDivide f => Monoidal (,) (FDivide ## f) where
  monoidal = fdivide (\(a,_) -> a) (\(_,b) -> b)

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
class    (forall x y. f x =# f y) => Phantom f
instance (forall x y. f x =# f y) => Phantom f
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



class (Monoidal (,) f, Map f) => Apply f where ap :: f (a -> b) -> f a -> f b
newtype instance (Apply ## f) a = Apply (f a)
  deriving newtype (Apply, Map)
  deriving (Remap,Map#) via Map ## Apply ## f
instance Apply f => Monoidal (,) (Apply ## f) where monoidal = ap < map (,)

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

newtype instance (Monad ## m) a = Monad (m a)
  deriving newtype (Monad, Applicative, Pure)
  deriving (Monoidal (,), Map, Remap, Map#) via Applicative ## Monad ## m
instance Monad m => Apply (Monad ## m) where
  ap (Monad mab) (Monad ma) = Monad ((`bind` mab) \ ab -> (`bind` ma) (pure < (ab $)))

-- * IsK
type family KVal t where KVal (K a) = a
class (Map f, f ~ K (KVal f), c (KVal f)) => IsK c f
instance c a => IsK c (K a)
type family LeftF t where LeftF (E a) = a
class (Map f, f ~ E (LeftF f)) => IsEither f
instance IsEither (E a)

deriving via Phantom ## K a instance Map (K a)
deriving via Phantom ## K a instance Map# (K a)
deriving via Phantom ## K a instance Remap (K a)
instance c ==> Pure => TraverseC c (K a) where traverseC _ (K a) = pure (K a)

map_traverseC :: (I ~ f, Map t) => (a -> f b) -> t a -> f (t b)
map_traverseC = (I<) < map < (unI<)
instance Semigroup a => Apply (K a) where ap (K a) (K b) = K (a . b)
deriving via Apply ## K a instance Semigroup a => Monoidal (,) (K a)
instance Monoid a => Pure (K a) where pure _ = K nil -- TODO: check this vs one
instance Monoid a => Applicative (K a)
instance Monoid a => Distribute (K a) where distribute _ = K nil
instance Monoid a => Monad (K a) where bind _ = coerce

instance Pure I where pure = I
instance Apply I where ap = coerce
deriving via Apply ## I instance Monoidal (,) I
instance Applicative I
instance Monad I where bind = coerce
instance Map I where map = coerce
deriving via Representational ## I instance Map# I
deriving via Map ## I instance Remap I
instance c ==> Map# => TraverseC c I where traverseC f (I a) = map# I (f a)
instance Bimap (,) where bimap f g (a,b) = (f a, g b)
instance LMap (,) where lmap f (a,x) = (f a, x)



deriving newtype instance Semigroup a => Semigroup (I a)
instance Semigroup a => Act (I a) (I a) where act (I a) (I b) = I (act a b)
deriving newtype instance Nil a => Nil (I a)
deriving newtype instance Monoid a => Monoid (I a)
{-instance TraverseC Wrap I    where traverseC = map_traverseC-}
instance Distribute I where distribute (fia :: f (I a)) = I (map# unI fia)


deriving via Representational ## (,) x instance Map# ((,) x)
deriving via Map ## (,) x instance Remap ((,) x)
instance Map ((,) x) where map f (x,a) = (x, f a)
instance c ==> Remap => TraverseC c ((,) x) 
  where traverseC f (x,a) = remap (\(_,b) -> b) (x,) (f a)

instance Monad P.IO where bind f io = io P.>>= f
instance Applicative P.IO
instance Apply P.IO where ap = (P.<*>)
deriving via Apply ## P.IO instance Monoidal (,) P.IO
instance Pure P.IO where pure = P.pure
instance Map P.IO where map = P.fmap
deriving via Map ## P.IO instance Remap P.IO
deriving via Representational ## P.IO instance Map# P.IO

instance (Map f, Map g) => Map (O f g)
  where map f (O fg) = O (map (map f) fg)
{-instance (Map f, Map g) => TraverseC Wrap (O f g) where traverseC = map_traverseC-}
deriving via Remap ## O f g instance (Remap f, Remap g) => Map# (O f g)
instance (Remap f, Remap g) => Remap (O f g)
  where remap f g (O fg) = O (remap (remap g f) (remap f g) fg)
instance (c ==> Map#, TraverseC c f, TraverseC c g) => TraverseC c (O f g) where
  traverseC f (O fg) = O `map#` traverseC @c (traverseC @c f) fg

instance FZero [] where fzero = [] -- TODO: fix this
instance Empty [] where empty = []
deriving via Representational ## [] instance Map# []
deriving via Map ## [] instance Remap []
{-deriving via Def1 (TraverseC Wrap) [] instance Map []-}
instance Map [] where map = P.map
instance Pure [] where pure a = [a]
instance (c ==> Applicative) => TraverseC c [] where
  traverseC f = go where
    go = \case
      [] -> pure []
      a : as -> (:) `map` f a `ap` go as

instance Map ((->) x) where map f g = \a ->  f (g a)
deriving via Representational ## (->) x instance Map# ((->) x)
deriving via Map ## (->) x instance Remap ((->) x)
instance Distribute ((->) x) where distribute fxa = \x -> map ($ x) fxa
{-instance TraverseC Wrap ((->) x) where traverseC = map_traverseC-}

deriving via Representational ## E x instance Map# (E x)
deriving via Map ## E x instance Remap (E x)
instance Map    (E x) where map f     = \case {L x -> L x; R a -> R (f a)}
instance Bimap E where bimap f g = \case {L a -> L $ f a; R b -> R $ g b}
instance LMap E where lmap f = bimap f id -- TODO: fix this with via
{-instance Monoid x => FAdd (E x) where-}
  
{-instance Monoid x => Semigroup (Add (E x a)) where nil = L nil-}
{-instance Monoid x => Monoid (Add (E x a)) where nil = L nil-}
{-instance Monoid a => Monoid (Times (E x a)) where one = R nil-}
instance Pure (E x)   where pure = R
instance (forall f. c f => (Pure f, Map f)) => TraverseC c (E x) where
  traverseC afb = \case {L x -> pure (L x); R a -> map R (afb a)}

-- | A @Monoidal@ functor over some associative monoidal product @t@
-- prop> remap (bimap f p) (bimap g q) (monoidal fa fb) = remap f g fa `monoidal` remap p q fb
class (Bimap t, Remap f) => Monoidal t f where monoidal :: f a -> f b -> f (a `t` b)
-- | remap f g fzero = 
class Remap f => FZero f where
  fzero :: f X
  fzero = lose id
  lose :: (a -> X) -> f a
  lose f = remap f (\case{}) fzero
-- | Covariant 'FZero' can be 'empty' for any type.
class (FZero f, Map f) => Empty f where
  empty :: f a
  empty = map absurd fzero

newtype Endo a = Endo (a -> a) deriving Map# via Representational ## Endo
instance Remap Endo where remap ba ab (Endo aa) = Endo $ ba > aa > ab
instance FZero Endo where fzero = Endo (\case{})
instance Monoidal (,) Endo where monoidal (Endo aa) (Endo bb) = Endo \ (a,b) -> (aa a,bb b)
instance Monoidal E Endo where monoidal (Endo aa) (Endo bb) = Endo $ bimap aa bb

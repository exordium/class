{-# language UndecidableInstances, UndecidableSuperClasses #-}
{-# language MagicHash #-}
{-# language DeriveFunctor, DeriveTraversable, DeriveFoldable #-}
module Functor where
import qualified Data.Coerce as GHC
import Data
import Type.I
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
instance Remap f => MapRep (Remap ## f) where mapRep f !x = remap coerce f x

newtype instance (Map ## f) a = Map (f a) deriving newtype Map
instance Map f => Remap (Map ## f) where remap _ = map
instance Map f => MapRep (Map ## f) where mapRep _ !x = map coerce x
instance Map f => P.Functor (Map ## f) where fmap = map
instance Map f => TraverseC Wrap (Map ## f) where
  traverseC afb (Map ta) = pure < Map $ map (afb > unwrap) ta

newtype instance (Representational ## f) a = Representational (f a)
instance Representational f => MapRep (Representational ## f) where mapRep _ = coerce


newtype instance (Pure ## f) a = Pure (f a)
  deriving newtype (Pure,Map)
  deriving (Remap,MapRep) via Map ## f

newtype instance (Applicative ## f) a = Applicative (f a)
  deriving newtype (Applicative,Pure,Apply)
  deriving (Monoidal (,)) via Apply ## f
  deriving (P.Functor,Remap,MapRep) via Map ## f

instance Applicative f => Map (Applicative ## f) where map f = (pure f |$|)

instance Applicative f => P.Applicative (Applicative ## f) where
  pure = pure
  (<*>) = (|$|)

-- | @f@ is a Monad-Module over @m@
class Monad m => Bound m f where bound :: (a -> m b) -> f a -> f b
instance {-# overlappable #-} Monad m => Bound m m where bound = bind
instance Bound Maybe [] where
  bound f = go where
    go [] = []
    go ((f -> Nothing):as)  =     go as
    go ((f -> Just b) :as)  = b : go as

-- | 
-- @filter@ must match default implementation
---- TODO: check if this class is necessary for performance
class Bound Maybe f => Filter f where 
  filter :: (a -> Bool) -> f a -> f a
  filter f = bound \ a -> case f a of {False -> Nothing; True -> Just a}
instance {-# overlappable #-} Bound Maybe f => Filter f
instance Filter [] where filter = P.filter


class Remap f => Map f where
  map :: (a -> b) -> f a -> f b
  (!@) :: b -> f a -> f b
  (!@) b = map \ _ -> b
($@) :: Map f => (a -> b) -> f a -> f b
($@) = map

--
-- | Covariant E-monoidal functors can be appended
class (forall x. Semigroup (f x), Monoidal E f, Map f) => Append f where
  append :: f a -> f a -> f a
  append fa fa' = map (\case L a -> a; R b -> b) (fa `monoidal` fa')

newtype instance (Append ## f) a = Append (f a)
  deriving newtype (Append, Map)
  deriving (Remap,MapRep) via Map ## f
instance Append f => Monoidal E (Append ## f) where
  monoidal (Append fa) (Append fb) = Append $ append (map L fa) (map R fb)
instance Append f => Semigroup ((Append ## f) a) where (.) = append


class Pure t => Distribute t where
  distribute :: Map f => f (t a) -> t (f a)
  distribute = collect \ x -> x
  zipWithF   :: Map f => (f a -> b) -> f (t a) -> t b
  zipWithF fab = \fta -> fab `map` distribute fta
  collect :: Map f => (a -> t b) -> f a -> t (f b)
  collect f a = zipWithF (\x -> x) (map f a)

newtype instance (Stock ## f) a = Stock1 (f a)
  deriving newtype (P.Functor,P.Foldable,P.Applicative, P.Monad)
  deriving (MapRep, Remap) via Map ## Stock ## f
  deriving (Monoidal (,)) via Apply ## Stock ## f
instance P.Traversable f => P.Traversable (Stock ## f) where
  traverse afb (Stock1 ta) = P.fmap Stock1 (P.traverse afb ta)
instance P.Applicative f => Pure (Stock ## f) where pure = P.pure
instance P.Applicative f => Apply (Stock ## f) where (|$|) = (P.<*>)
instance P.Applicative f => Applicative (Stock ## f)
instance P.Monad f => Monad (Stock ## f) where bind f = (P.>>= f)
instance P.Traversable f => TraverseC Applicative (Stock ## f) where
  traverseC afb (Stock1 ta) = mapRep Stock1 < (\(Applicative x) -> x)
                            $ P.traverse (Applicative < afb) ta

instance P.Functor f => Map (Stock ## f) where map = P.fmap
data V2 a = V2 {v2a :: a, v2b :: a}
  deriving stock (P.Functor, P.Traversable, P.Foldable)
  deriving (Remap, Map) via Stock ## V2
  deriving MapRep via Representational ## V2

newtype instance (Distribute ## t) a = Distribute (t a)
  deriving (Remap, MapRep) via Map ## Distribute ## t
instance Distribute t => Map (Distribute ## t) where
  map ab (Distribute ta) = Distribute $ zipWithF (unI > ab) (I ta)
instance Distribute t => Distribute (Distribute ## t) where
  distribute = Distribute < (mapRep (\(Distribute ta) -> ta) > distribute)
  collect (coerce -> atb) = Distribute < collect atb
instance Distribute t => Pure (Distribute ## t) where
  pure = Distribute < mapRep unK < distribute < K



class Remap f => Comap f where comap :: (b -> a) -> f a -> f b

newtype instance (Comap ## f) a = Comap (f a)
  deriving newtype Comap
  deriving MapRep via Remap ## f
instance Comap f => Remap (Comap ## f) where remap f _ = comap f

class (Comap f, Monoidal (,) f) => FDivide f where -- TODO: check this is needed for performance
  fdivide :: (x -> a) -> (x -> b) -> f a -> f b -> f x
  fdivide f g fa fb = comap (\x -> (f x, g x)) (fa `monoidal` fb)
instance {-# overlappable #-} (Monoidal (,) f, Comap f) => FDivide f

newtype instance (FDivide ## f) a = FDivide (f a)
  deriving newtype (FDivide,Comap)
  deriving (Remap,MapRep) via Comap ## f


instance FDivide f => Monoidal (,) (FDivide ## f) where
  monoidal = fdivide (\(a,_) -> a) (\(_,b) -> b)

class (Comap f, Monoidal E f) => Choose f where
  choose :: (x -> E a b) -> f a -> f b -> f x
  choose f fa fb = comap f (monoidal fa fb)
instance {-#overlappable #-} (Comap f, Monoidal E f) => Choose f

newtype instance (Choose ## f) a = Choose (f a)
  deriving newtype (Choose,Comap)
  deriving (Remap,MapRep) via Comap ## f
instance Choose f => Monoidal E (Choose ## f) where monoidal = choose id
  

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
class    ((forall a b. a =# b => f a =# f b),MapRep f) => Representational f
instance ((forall a b. a =# b => f a =# f b),MapRep f) => Representational f
representational :: forall b a f. (a =# b, Representational f) => f a -> f b
{-# INLINE representational #-}
representational = GHC.coerce

-- | 'Phantom' types can ignore their type parameter. Instances are automatically provided by GHC
class    (forall x y. f x =# f y) => Phantom f
instance (forall x y. f x =# f y) => Phantom f
phantom :: forall b a f. Phantom f => f a -> f b
phantom = GHC.coerce @(f a) @(f b)

newtype instance (Phantom ## f) a = Phantom (f a)

instance Phantom f => Map (Phantom ## f) where map _ = coerce
instance Phantom f => MapRep (Phantom ## f) where mapRep _ = coerce
instance Phantom f => Remap (Phantom ## f) where remap _ _ = coerce
instance (Phantom f, Append f) => Apply (Phantom ## f) where
  Phantom fab |$| Phantom fa = Phantom < phantom $ fab `append` phantom fa
deriving via Apply ## Phantom ## f instance (Append f, Phantom f) => Monoidal (,) (Phantom ## f)
instance (Phantom f, Empty f) => Pure (Phantom ## f) where pure _ = Phantom empty
instance (Alternative f, Phantom f) => Applicative (Phantom ## f)
instance (Alternative m, Phantom m) => Monad (Phantom ## m) where bind _ = coerce
phantom_traverseC :: (c ==> Pure, c f, Phantom t) => (a -> f b) -> t a -> f (t b)
phantom_traverseC _ = pure < phantom
-- Doesn't actually work because deriving via can't get under @f@, use above instead
instance (Phantom f, c ==> Pure) => TraverseC c (Phantom ## f) where
  traverseC _ (Phantom k) = (pure < Phantom < phantom) k

class MapRep f where mapRep :: a =# b => (a -> b) -> f a -> f b

mapAs :: forall b a f. (MapRep f, a =# b) => f a -> f b
mapAs = mapRep (coerce @b)

class MapRep f => Remap f where remap :: (b -> a) -> (a -> b) -> f a -> f b
remap_mapRep :: (Remap f, a =# b) => (a -> b) -> f a -> f b
remap_mapRep f !x = remap coerce f x
(#@) :: (MapRep f, a =# b) => (a -> b) -> f a -> f b
(#@) = mapRep
strong :: Remap f => a -> f b -> f (a,b)
strong a = remap (\(_,b) -> b) (a,)

class ({- forall cc. (cc ==> c) => TraverseC cc t, c ==> MapRep, -} Map t) => TraverseC c t where
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


class (Monoidal (,) f, Map f) => Apply f where
  (|$|) :: f (a -> b) -> f a -> f b
  (|$) :: f a -> (a -> b -> c) -> f b -> f c
  fa |$ f = (map f fa |$|)
($|) :: (f b -> f c) -> f b -> f c
f $| fb = f fb
newtype instance (Apply ## f) a = Apply (f a)
  deriving newtype (Apply, Map)
  deriving (Remap,MapRep) via Map ## Apply ## f
instance Apply f => Monoidal (,) (Apply ## f) where monoidal fa = ((,) $@ fa |$|)

class (Map f, Pure f, Apply f) => Applicative f
class Applicative m => Monad m where bind :: (a -> m b) -> m a -> m b
(>>=) :: Monad m => m a -> (a -> m b) -> m b
(>>=) m = (`bind` m)
infixl 1 >>=
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

extract :: TraverseC (IsK Stock) f => f a -> a
extract = traverseC @(IsK Stock) K > unK

-- * Wrap
class (Distribute f, Monad f, Representational f, forall x. x =# f x) => Wrap f
instance (Distribute f, Monad f, Representational f, forall x. x =# f x) => Wrap f
unwrap :: Wrap f => f a -> a
unwrap = coerce
newtype instance (Wrap ## f) a = Wrap (f a)
instance Wrap f => Monad (Wrap ## f) where bind = coerce
instance Wrap f => Distribute (Wrap ## f) where distribute = pure < mapRep unwrap
deriving via Representational ## f instance Wrap f => MapRep (Wrap ## f)
instance Wrap f => Map (Wrap ## f) where map = coerce
deriving via Map ## Wrap ## f instance Wrap f => Remap        (Wrap ## f)
deriving via Apply ## Wrap ## f instance Wrap f => Monoidal (,) (Wrap ## f)
instance Wrap f => Applicative  (Wrap ## f)
instance Wrap f => Pure (Wrap ## f) where pure = coerce
instance Wrap f => Apply (Wrap ## f) where (|$|) = unwrap > coerce

wrap_traverseC :: (c ==> MapRep, c f, Wrap t) => (a -> f b) -> t a -> f (t b)
wrap_traverseC f (unwrap -> a) = mapRep pure $ f a

instance (Wrap f, c ==> MapRep) => TraverseC c (Wrap ## f) where
  traverseC f (Wrap (unwrap -> a)) = mapRep pure $ f a

newtype instance (Monad ## m) a = Monad (m a)
  deriving newtype (Monad, Applicative, Pure)
  deriving (Monoidal (,), Map, Remap, MapRep) via Applicative ## Monad ## m
instance Monad m => Apply (Monad ## m) where
  Monad mab |$| Monad ma = Monad (mab >>= \ ab -> ma >>= (ab $) > pure)

-- * IsK
type family KVal t where KVal (K a) = a
class (Map f, f ~ K (KVal f), c (KVal f)) => IsK c f
instance c a => IsK c (K a)
type family LeftF t where LeftF (E a) = a
class (Map f, f ~ E (LeftF f)) => IsEither f
instance IsEither (E a)






-- | A @Monoidal@ functor over some associative monoidal product @t@
-- prop> remap (bimap f p) (bimap g q) (monoidal fa fb) = remap f g fa `monoidal` remap p q fb
class (Bimap t, Remap f) => Monoidal t f where monoidal :: f a -> f b -> f (a `t` b)
-- | remap f g fzero = 
class Remap f => FZero f where
  fzero :: f X
  fzero = lose id
  lose :: (a -> X) -> f a
  lose f = remap f absurd fzero
-- | Covariant 'FZero' can be 'empty' for any type.
class (FZero f, Map f) => Empty f where
  empty :: f a
  empty = map absurd fzero

newtype instance (Empty ## f) a = Empty (f a)
  deriving newtype (Empty,Map)
  deriving (Remap,MapRep) via Map ## f
instance Empty f => FZero (Empty ## f) where fzero = empty



class (Append f, Empty f) => Alternative f


-- * Defaults


-- * Instances

-- ** Maybe
instance Pure Maybe where pure = Just
instance Monad Maybe where bind f = \case {Nothing -> Nothing; Just a -> f a}
deriving via Monad ## Maybe instance Applicative Maybe
deriving via Monad ## Maybe instance Apply Maybe
deriving via Monad ## Maybe instance Monoidal (,) Maybe
deriving via Monad ## Maybe instance Map Maybe
deriving via Monad ## Maybe instance Remap Maybe
deriving via Representational ## Maybe instance MapRep Maybe

-- ** E
deriving via Representational ## E x instance MapRep (E x)
deriving via Map ## E x instance Remap (E x)
instance Map    (E x) where map f     = \case {L x -> L x; R a -> R (f a)}
instance Bimap E where bimap f g = \case {L a -> L $ f a; R b -> R $ g b}
instance LMap E where lmap f = bimap f id -- TODO: fix this with via
instance Pure (E x)   where pure = R
instance (forall f. c f => (Pure f, Map f)) => TraverseC c (E x) where
  traverseC afb = \case {L x -> pure (L x); R a -> map R (afb a)}

-- ** @(->)@
instance Map ((->) x) where map f g = \a ->  f (g a)
deriving via Representational ## (->) x instance MapRep ((->) x)
deriving via Map ## (->) x instance Remap ((->) x)
instance Distribute ((->) x) where distribute fxa = \x -> map ($ x) fxa
instance Pure ((->) x) where pure = (!)


-- ** @[]@
instance FZero [] where fzero = [] -- TODO: fix this
instance Empty [] where empty = []
deriving via Representational ## [] instance MapRep []
deriving via Map ## [] instance Remap []
{-deriving via Def1 (TraverseC Wrap) [] instance Map []-}
instance Map [] where map = P.map
instance Pure [] where pure a = [a]
instance (c ==> Applicative) => TraverseC c [] where
  traverseC f = go where
    go = \case
      [] -> pure []
      a : as -> (:) $@ f a |$| go as

-- ** @(,)@
deriving via Representational ## (,) x instance MapRep ((,) x)
deriving via Map ## (,) x instance Remap ((,) x)
instance Map ((,) x) where map f (x,a) = (x, f a)
instance Bimap (,) where bimap f g (a,b) = (f a, g b)
instance LMap (,) where lmap f (a,x) = (f a, x)
instance c ==> Remap => TraverseC c ((,) x) 
  where traverseC f (x,a) = remap (\(_,b) -> b) (x,) (f a)

-- ** @I@
deriving via Wrap ## I instance Pure I
deriving via Wrap ## I instance Apply I
deriving via Wrap ## I instance Monoidal (,) I
deriving via Wrap ## I instance Monad I
deriving via Wrap ## I instance Map I
instance Applicative I
deriving via Wrap ## I instance MapRep I
deriving via Wrap ## I instance Remap I
instance c ==> MapRep => TraverseC c I where traverseC f (I a) = mapRep I (f a)
instance Distribute I where distribute (fia :: f (I a)) = I (mapRep unI fia)

-- ** @K@
deriving via Phantom ## K a instance Map (K a)
deriving via Phantom ## K a instance MapRep (K a)
deriving via Phantom ## K a instance Remap (K a)
instance c ==> Pure => TraverseC c (K a) where traverseC = phantom_traverseC @c

instance Nil a => Empty (K a) where empty = K nil
deriving via Empty ## K a instance Nil a => FZero (K a)
instance Semigroup a => Append (K a) where K a `append` K b = K $ a . b
instance Monoid a => Alternative (K a)
deriving via Append ## K a instance Semigroup a => Monoidal E (K a)
deriving via (Append ## K a) x instance Semigroup a => Semigroup (K a x)
deriving via Phantom ## K a instance Semigroup a => Apply (K a)
deriving via Apply ## K a instance Semigroup a => Monoidal (,) (K a)
deriving via Phantom ## K a instance Monoid a => Pure (K a)
instance Monoid a => Applicative (K a)
instance Monoid a => Distribute (K a) where distribute _ = K nil
deriving via Phantom ## K a instance Monoid a => Monad (K a)

-- ** IO
instance Monad P.IO where bind f io = io P.>>= f
instance Applicative P.IO
instance Apply P.IO where (|$|) = (P.<*>)
deriving via Apply ## P.IO instance Monoidal (,) P.IO
instance Pure P.IO where pure = P.pure
instance Map P.IO where map = P.fmap
deriving via Map ## P.IO instance Remap P.IO
deriving via Representational ## P.IO instance MapRep P.IO

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
import qualified GHC.TypeLits as P
import qualified Data.Proxy as P
import Types
import Fun
{-import {-# source #-} Control-}
import qualified Data.Set as PS
import Reflect


-- * Classes

class Map_ f => Remap f where remap :: (b -> a) -> (a -> b) -> f a -> f b
newtype instance (Remap ## f) a = Remap (f a) deriving newtype Remap
instance Remap f => Map_ (Remap ## f) where map_ f !x = remap coerce f x
-- | Every haskell functor is Strong
strong :: Remap f => a -> f b -> f (a,b)
strong a = remap (\(_,b) -> b) (a,)

class Remap f => Map f where
  map :: (a -> b) -> f a -> f b
  mapConst :: b -> f a -> f b
  mapConst b = map \ _ -> b
newtype instance (Map ## f) a = Map (f a) deriving newtype Map
instance Map f => Remap (Map ## f) where remap _ = map
instance Map f => Map_ (Map ## f) where map_ _ !x = map coerce x
instance Map f => P.Functor (Map ## f) where fmap = map
instance Map f => TraverseC Wrap (Map ## f) where
  traverseC afb (Map ta) = pure < Map $ map (afb > unwrap) ta
($@) :: Map f => (a -> b) -> f a -> f b
($@) = map
(!@) :: Map f => b -> f a -> f b
(!@) = mapConst

-- | Traverse over a container with a functor 
 {-forall cc. (cc ==> c) => TraverseC cc t, c ==> Map_, -}
class Map t => TraverseC c t where
  traverseC :: c f => (a -> f b) -> t a -> f (t b)
  traverseC afb ta = sequence @c (map afb ta)
  sequence :: c f => t (f a) -> f (t a)
  sequence = traverseC @c \ x -> x

traverse :: (TraverseC Applicative t,Applicative f) => (a -> f b) -> t a -> f (t b)
traverse = traverseC @Applicative
for, (@@) :: (TraverseC Applicative t,Applicative f) => t a -> (a -> f b) -> f (t b)
for t f = traverseC @Applicative f t
(@@) = for

traverse1 :: (TraverseC Apply t,Apply f) => (a -> f b) -> t a -> f (t b)
traverse1 = traverseC @Apply
for1 :: (TraverseC Apply t,Apply f) => t a -> (a -> f b) -> f (t b)
for1 t = (`traverse1` t)

traverse0 :: (TraverseC Pure t,Pure f) => (a -> f b) -> t a -> f (t b)
traverse0 = traverseC @Pure
for0 :: (TraverseC Pure t,Pure f) => t a -> (a -> f b) -> f (t b)
for0 t = (`traverse0` t)

traverse_ :: (TraverseC Remap t,Remap f) => (a -> f b) -> t a -> f (t b)
traverse_ = traverseC @Remap
for_ :: (TraverseC Remap t,Remap f) => t a -> (a -> f b) -> f (t b)
for_ t = (`traverse_` t)

fold :: (TraverseC (Applicative & Comap) t, Monoid m) => (a -> m) -> t a -> m
fold f = traverseC @(Applicative & Comap) (f > K) > unK
(@.) :: (TraverseC (Applicative & Comap) t, Monoid m) => t a -> (a -> m) -> m
(@.) t = (`fold` t)

fold1 :: (TraverseC (Apply & Comap) t, Monoid m) => (a -> m) -> t a -> m
fold1 f = traverseC @(Apply & Comap) (f > K) > unK

extract :: TraverseC (Map & Comap) f => f a -> a
extract = traverseC @(Map & Comap) K > unK

extract0 :: (TraverseC (Pure & Comap) f, Nil m) => (a -> m) -> f a -> m
extract0 f = traverseC @(Pure & Comap) (f > K) > unK

(@?) :: (TraverseC (Pure & Comap) t, Nil a) => t a -> a -> a
(@?) t a = usingInst (Reified_Nil a) do extract0 Instance t

data instance Reified Nil a = Reified_Nil a
instance Reifies s (Reified Nil a) => Nil (Instance Nil a s) where
  nil = let Reified_Nil a = reflect' @s
         in Instance @Nil a

-- * Monoidal Functors

-- | A @Monoidal@ functor over some associative monoidal product @t@
-- prop> remap (bimap f p) (bimap g q) (monoidal fa fb) = remap f g fa `monoidal` remap p q fb
class (Bimap t, Remap f) => Monoidal t f where monoidal :: f a -> f b -> f (a `t` b)
-- | A @Pure f@ is a pointed functor with a particular inhabited shape singled out
-- Free Theorem:
-- prop> pure < f = map f < pure

class ({- Lifting Monoid One f, -} Remap f) => Pure f where
  {-# minimal pure | fone #-}
  pure :: a -> f a
  pure a = remap (()!) (a!) fone
  fone :: f ()
  fone = pure ()
newtype instance (Pure ## f) a = Pure (f a)
  deriving newtype (Pure,Map)
  deriving (Remap,Map_) via Map ## f


class (Monoidal (,) f, Map f) => Apply f where
  ap :: f (a -> b) -> f a -> f b
  ap = liftA2 id
  liftA2 :: (a -> b -> c) -> f a -> f b -> f c
  liftA2 f = ap < map f
newtype instance (Apply ## f) a = Apply (f a)
  deriving newtype (Apply, Map)
  deriving (Remap,Map_) via Map ## Apply ## f
instance Apply f => Monoidal (,) (Apply ## f) where monoidal fa = ((,) $@ fa |$|)
(|$|) :: Apply f => f (a -> b) -> f a -> f b
(|$|) = ap
-- | Infix synonym for @liftA2@ to be used with @($|)@. Ex:
--
-- >>> fx |$ zip $| fy === liftA2 zip fx fy
(|$) :: Apply f => f a -> (a -> b -> c) -> f b -> f c
fa |$ f = liftA2 f fa
-- | Convenience function used with @(|$)@ to create infix brackets. Ex:
--
-- >>> fx |$ zip $| fy === liftA2 zip fx fy
($|) :: (f b -> f c) -> f b -> f c
f $| fb = f fb

-- | prop> @pure f |$| fa@ = map f fa@
--   prop> ff |$| pure a = map ($ a) ff
class (Map f, Pure f, Apply f) => Applicative f
newtype instance (Applicative ## f) a = Applicative (f a)
  deriving newtype (Applicative,Pure,Apply)
  deriving (Monoidal (,)) via Apply ## f
  deriving (P.Functor,Remap,Map_) via Map ## f
instance Applicative f => Map (Applicative ## f) where map f = (pure f |$|)
instance Applicative f => P.Applicative (Applicative ## f) where
  pure = pure
  (<*>) = ap

-- | distribute < imap (imap < iab) = imap (imap < flip iab) < distribute
class Applicative t => Distribute t where
  distribute :: Map f => f (t a) -> t (f a)
  distribute = collect \ x -> x
  zipWithF   :: Map f => (f a -> b) -> f (t a) -> t b
  zipWithF fab = \fta -> fab `map` distribute fta
  collect :: Map f => (a -> t b) -> f a -> t (f b)
  collect f a = zipWithF (\x -> x) (map f a)
newtype instance (Distribute ## t) a = Distribute (t a)
  deriving (Remap, Map_) via Map ## Distribute ## t
  deriving anyclass Applicative
instance Distribute t => Map (Distribute ## t) where
  map ab (Distribute ta) = Distribute $ zipWithF (unI > ab) (I ta)
instance Distribute t => Distribute (Distribute ## t) where
  distribute = Distribute < (map_ (\(Distribute ta) -> ta) > distribute)
  collect (coerce -> atb) = Distribute < collect atb
instance Distribute t => Pure (Distribute ## t) where
  pure = Distribute < map_ unK < distribute < K
deriving via Apply ## Distribute ## t
  instance Distribute t => Monoidal (,) (Distribute ## t)
instance Distribute t => Apply (Distribute ## t) where
  liftA2 f (Distribute ta) (Distribute tb) = Distribute
    $ zipWithF (\(V2 (L a) (R b)) -> f a b) (V2 (map L ta) (map R tb))
  Distribute tab `ap` Distribute ta = Distribute
    $ zipWithF (\(V2 (L f) (R a)) -> f a) (V2 (L $@ tab) (R $@ ta))

-- | A @FZero f@ has a partiuclar uninhabited singled out.
-- Dual to 'Pure'
class Remap f => FZero f where
  {-# minimal fzero | lose #-}
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
  deriving (Remap,Map_) via Map ## f
instance Empty f => FZero (Empty ## f) where fzero = empty

class (Append f, Empty f) => Alternative f

-- | Covariant E-monoidal functors can be appended
class (forall x. Op (f x), Monoidal E f, Map f) => Append f where
  append :: f a -> f a -> f a
  append fa fa' = map (\case L a -> a; R b -> b) (fa `monoidal` fa')
newtype instance (Append ## f) a = Append (f a)
  deriving newtype (Append, Map)
  deriving (Remap,Map_) via Map ## f
instance Append f => Monoidal E (Append ## f) where
  monoidal (Append fa) (Append fb) = Append $ append (map L fa) (map R fb)
instance Append f => Op ((Append ## f) a) where (.) = append

-- * Contravariant Functors
class Remap f => Comap f where comap :: (b -> a) -> f a -> f b

newtype instance (Comap ## f) a = Comap (f a)
  deriving newtype Comap
  deriving Map_ via Remap ## f
instance Comap f => Remap (Comap ## f) where remap f _ = comap f

class (Comap f, Monoidal (,) f) => FDivide f where -- TODO: check this is needed for performance
  fdivide :: (x -> a) -> (x -> b) -> f a -> f b -> f x
  fdivide f g fa fb = comap (\x -> (f x, g x)) (fa `monoidal` fb)
instance {-# overlappable #-} (Monoidal (,) f, Comap f) => FDivide f

newtype instance (FDivide ## f) a = FDivide (f a)
  deriving newtype (FDivide,Comap)
  deriving (Remap,Map_) via Comap ## f

instance FDivide f => Monoidal (,) (FDivide ## f) where
  monoidal = fdivide (\(a,_) -> a) (\(_,b) -> b)

class (Comap f, Monoidal E f) => Choose f where
  choose :: (x -> E a b) -> f a -> f b -> f x
  choose f fa fb = comap f (monoidal fa fb)
instance {-#overlappable #-} (Comap f, Monoidal E f) => Choose f

newtype instance (Choose ## f) a = Choose (f a)
  deriving newtype (Choose,Comap)
  deriving (Remap,Map_) via Comap ## f
instance Choose f => Monoidal E (Choose ## f) where monoidal = choose id

-- * Monads
class Applicative m => Monad m where bind :: (a -> m b) -> m a -> m b
newtype instance (Monad ## m) a = Monad (m a)
  deriving newtype (Monad, Applicative, Pure)
  deriving (Monoidal (,), Map, Remap, Map_) via Applicative ## Monad ## m
instance Monad m => Apply (Monad ## m) where
  Monad mab `ap` Monad ma = Monad (mab >>= \ ab -> ma >>= (ab $) > pure)
(>>=) :: Monad m => m a -> (a -> m b) -> m b
(>>=) m = (`bind` m)
infixl 1 >>=

-- | imap f . imap g = imap (\i -> f i . g i)
--   imap (\_ -> f) = map f
class Map f => IMap i f where
  {-# minimal imap #-}
  imap :: (i -> a -> b) -> f a -> f b
  adjust :: Eq' i => (a -> a) -> i -> f a -> f a
  adjust f i = imap (\i' a -> if i `eq` i' then f a else a)

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

class (LMap f, forall x. Map (f x)) => Bimap f where
  bimap :: (x -> a) -> (y -> b) -> f x y -> f a b
newtype instance (Bimap ### f) a b = Bimap (f a b)
  deriving newtype Bimap
  deriving (Remap, Map_) via Map ## f a
instance Bimap f => Map ((Bimap ### f) a) where map = bimap  id
instance Bimap f => LMap (Bimap ### f) where lmap = (`bimap` id)

class LMap f where lmap :: (a -> b) -> f a x -> f b x

-- * Coercions
class    ((forall a b. a =# b => f a =# f b),Map_ f) => Representational f
instance ((forall a b. a =# b => f a =# f b),Map_ f) => Representational f
newtype instance (Representational ## f) a = Representational (f a)
instance Representational f => Map_ (Representational ## f) where map_ _ = coerce
representational :: forall b a f. (a =# b, Representational f) => f a -> f b
representational = GHC.coerce
{-# INLINE representational #-}

-- | 'Phantom' types can ignore their type parameter. Instances are automatically provided by GHC
class    (forall x y. f x =# f y) => Phantom f
instance (forall x y. f x =# f y) => Phantom f
newtype instance (Phantom ## f) a = Phantom (f a)
instance Phantom f => Map (Phantom ## f) where map _ = coerce
instance Phantom f => Comap (Phantom ## f) where comap _ = coerce
instance Phantom f => Map_ (Phantom ## f) where map_ _ = coerce
instance Phantom f => Remap (Phantom ## f) where remap _ _ = coerce
instance (Phantom f, Append f) => Apply (Phantom ## f) where
  Phantom fab `ap` Phantom fa = Phantom < phantom $ fab `append` phantom fa
deriving via Apply ## Phantom ## f instance (Append f, Phantom f) => Monoidal (,) (Phantom ## f)
instance (Phantom f, Empty f) => Pure (Phantom ## f) where pure _ = Phantom empty
instance (Alternative f, Phantom f) => Applicative (Phantom ## f)
instance (Alternative m, Phantom m) => Monad (Phantom ## m) where bind _ = coerce
phantom_traverseC :: (c ==> Pure, c f, Phantom t) => (a -> f b) -> t a -> f (t b)
phantom_traverseC _ = pure < phantom
-- Doesn't actually work because deriving via can't get under @f@, use above instead
instance (Phantom f, c ==> Pure) => TraverseC c (Phantom ## f) where
  traverseC _ (Phantom k) = (pure < Phantom < phantom) k
phantom :: forall b a f. Phantom f => f a -> f b
phantom = GHC.coerce @(f a) @(f b)

-- | @Wrap@ed functors are (representationally) isomorphic to identity
class (Distribute f, Monad f, Representational f, forall x. x =# f x) => Wrap f
instance (Distribute f, Monad f, Representational f, forall x. x =# f x) => Wrap f
newtype instance (Wrap ## f) a = Wrap (f a)
instance Wrap f => Monad (Wrap ## f) where bind = coerce
instance Wrap f => Distribute (Wrap ## f) where distribute = pure < map_ unwrap
deriving via Representational ## f instance Wrap f => Map_ (Wrap ## f)
instance Wrap f => Map (Wrap ## f) where map = coerce
deriving via Map ## Wrap ## f instance Wrap f => Remap        (Wrap ## f)
deriving via Apply ## Wrap ## f instance Wrap f => Monoidal (,) (Wrap ## f)
instance Wrap f => Applicative  (Wrap ## f)
instance Wrap f => Pure (Wrap ## f) where pure = coerce
instance Wrap f => Apply (Wrap ## f) where ap = unwrap > coerce
wrap_traverseC :: (c ==> Map_, c f, Wrap t) => (a -> f b) -> t a -> f (t b)
wrap_traverseC f (unwrap -> a) = map_ pure $ f a
instance (Wrap f, c ==> Map_) => TraverseC c (Wrap ## f) where
  traverseC f (Wrap (unwrap -> a)) = map_ pure $ f a
unwrap :: Wrap f => f a -> a
unwrap = coerce

-- | Strictly map a coercion over a functor, 
-- using 'coerce' if it's 'Representational' or `remap` otherwise.
class Map_ f where map_ :: a =# b => (a -> b) -> f a -> f b
(#@) :: (Map_ f, a =# b) => (a -> b) -> f a -> f b
(#@) = map_
mapAs :: forall b a f. (Map_ f, a =# b) => f a -> f b
mapAs = map_ (coerce @b)

-- * IsK
type family KVal t where KVal (K a) = a
class (Map f, f ~ K (KVal f), c (KVal f)) => IsK c f
instance c a => IsK c (K a)
type family LeftF t where LeftF (E a) = a
class (Map f, f ~ E (LeftF f)) => IsEither f
instance IsEither (E a)


-- Instances --

-- Stock
newtype instance (Stock ## f) a = Stock1 (f a)
  deriving newtype (P.Functor,P.Foldable,P.Applicative, P.Monad)
  deriving (Map_, Remap) via Map ## Stock ## f
  deriving (Monoidal (,)) via Apply ## Stock ## f
instance P.Traversable f => P.Traversable (Stock ## f) where
  traverse afb (Stock1 ta) = P.fmap Stock1 (P.traverse afb ta)
instance P.Applicative f => Pure (Stock ## f) where pure = P.pure
instance P.Applicative f => Apply (Stock ## f) where ap = (P.<*>)
instance P.Applicative f => Applicative (Stock ## f)
instance P.Monad f => Monad (Stock ## f) where bind f = (P.>>= f)
instance P.Traversable f => TraverseC Applicative (Stock ## f) where
  traverseC afb (Stock1 ta) = map_ Stock1 < (\(Applicative x) -> x)
                            $ P.traverse (Applicative < afb) ta
instance P.Functor f => Map (Stock ## f) where map = P.fmap
data V2 a = V2 {v2a :: a, v2b :: a}
  deriving stock (P.Functor, P.Traversable, P.Foldable)
  deriving (Remap, Map) via Stock ## V2
  deriving Map_ via Representational ## V2
  deriving stock (P.Show)

-- Maybe
instance Pure Maybe where pure = Just
instance Monad Maybe where bind f = \case {Nothing -> Nothing; Just a -> f a}
deriving via Monad ## Maybe instance Applicative Maybe
deriving via Monad ## Maybe instance Apply Maybe
deriving via Monad ## Maybe instance Monoidal (,) Maybe
deriving via Monad ## Maybe instance Map Maybe
deriving via Monad ## Maybe instance Remap Maybe
deriving via Representational ## Maybe instance Map_ Maybe
instance c ==> Pure => TraverseC c Maybe where
  traverseC f = \case
    Nothing -> pure Nothing
    Just a -> remap (\case Just a -> a) Just $ f a

-- E
deriving via Representational ## E x instance Map_ (E x)
deriving via Map ## E x instance Remap (E x)
instance Bimap E where bimap f g = \case {L a -> L $ f a; R b -> R $ g b}
deriving via Bimap ### E instance LMap E
deriving via (Bimap ### E) a instance Map (E a)
instance Pure (E x)   where pure = R
instance c ==> Pure => TraverseC c (E x) where
  traverseC afb = \case {L x -> pure (L x); R a -> remap (\case R a -> a) R (afb a)}

-- (->)
instance Map ((->) x) where map f g = \a ->  f (g a)
deriving via Representational ## (->) x instance Map_ ((->) x)
deriving via Map ## (->) x instance Remap ((->) x)
instance Distribute ((->) x) where distribute fxa x = map ($ x) fxa
instance Pure ((->) x) where pure = (!)
instance Apply ((->) x) where ap iab ia = \i -> iab i $ ia i
instance Monoidal (,) ((->) x) where monoidal ia ib = \i -> (ia i, ib i)
instance Applicative ((->) x)


-- []
deriving via Empty            ## [] instance FZero []
deriving via Representational ## [] instance Map_ []
deriving via Map              ## [] instance Remap []
instance Empty [] where empty = []
instance Map   [] where map = P.map
instance Pure  [] where pure a = [a]
instance (c ==> Applicative) => TraverseC c [] where
  traverseC f = go where
    go = \case
      [] -> pure []
      a : as -> (:) $@ f a |$| go as
instance IMap P.Int [] where
  imap f = go 0 where
    go _ [] = []
    go i (a:as) = f i a : go (P.succ i) as

-- (,)
deriving via Representational ## (,) x instance Map_ ((,) x)
deriving via Map              ## (,) x instance Remap ((,) x)
instance Map  ((,) x) where map f (x,a)     = (  x, f a)
instance Bimap (,)    where bimap f g (a,b) = (f a, g b)
instance LMap  (,)    where lmap f (a,x)    = (f a,   x)
instance c ==> Remap => TraverseC c ((,) x) 
  where traverseC f (x,a) = remap (\(_,b) -> b) (x,) (f a)

-- I
deriving via Wrap ## I instance Pure I
deriving via Wrap ## I instance Apply I
deriving via Wrap ## I instance Monoidal (,) I
deriving via Wrap ## I instance Monad I
deriving via Wrap ## I instance Map I
instance Applicative I
deriving via Wrap ## I instance Map_ I
deriving via Wrap ## I instance Remap I
instance c ==> Map_ => TraverseC c I where traverseC f (I a) = map_ I (f a)
instance Distribute I where distribute (fia :: f (I a)) = I (map_ unI fia)

-- K
deriving via Phantom ## K a instance Map (K a)
deriving via Phantom ## K a instance Comap (K a)
deriving via Phantom ## K a instance Map_ (K a)
deriving via Phantom ## K a instance Remap (K a)
instance c ==> Pure => TraverseC c (K a) where traverseC = phantom_traverseC @c
instance Nil a => Empty (K a) where empty = K nil
deriving via Empty ## K a instance Nil a => FZero (K a)
instance Op a => Append (K a) where K a `append` K b = K $ a . b
instance Monoid a => Alternative (K a)
deriving via Append ## K a instance Op a => Monoidal E (K a)
deriving via (Append ## K a) x instance Op a => Op (K a x)
deriving via Phantom ## K a instance Op a => Apply (K a)
deriving via Apply ## K a instance Op a => Monoidal (,) (K a)
deriving via Phantom ## K a instance Nil a => Pure (K a)
instance Monoid a => Applicative (K a)
instance Monoid a => Distribute (K a) where distribute _ = K nil
deriving via Phantom ## K a instance Monoid a => Monad (K a)

-- IO
instance Monad P.IO where bind f io = io P.>>= f
instance Applicative P.IO
instance Apply P.IO where ap = (P.<*>)
deriving via Apply ## P.IO instance Monoidal (,) P.IO
instance Pure P.IO where pure = P.pure
instance Map P.IO where map = P.fmap
deriving via Map ## P.IO instance Remap P.IO
deriving via Representational ## P.IO instance Map_ P.IO


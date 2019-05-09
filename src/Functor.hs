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
import Type.These
import qualified Prelude as P
import qualified Control.Monad.Fix as P
import qualified GHC.TypeLits as P
import qualified Data.Proxy as P
import Types
import Fun
{-import {-# source #-} Control-}
import qualified Data.Set as PS
import Reflect
import qualified Data.Map as PM


-- * Classes

class Map_ f => Remap f where
  remap :: (b -> a) -> (a -> b) -> f a -> f b
  {-map__ :: (a =# b) => (Representational f => f a -> f b) -> (a -> b) -> f a -> f b-}
  {-map__ _ _ !x = remap coerce coerce x-}
newtype instance (Remap ## f) a = Remap (f a)
instance Remap f => Map_ (Remap ## f) where
  mapAs (Remap (!x)) = Remap $ remap coerce coerce x
-- | Every haskell functor is Strong
strong :: Remap f => a -> f b -> f (a,b)
strong a = remap (\(_,b) -> b) (a,)

class (Remap f {- ,Traverses Wrap f -}) => Map f where
  map :: (a -> b) -> f a -> f b
  mapConst :: b -> f a -> f b
  mapConst b = map \ _ -> b
newtype instance (Map ## f) a = Map (f a) deriving newtype Map
  deriving Map_ via Remap ## f
instance Map f => Remap (Map ## f) where remap _ = map
instance Map f => P.Functor (Map ## f) where fmap f = coerce (map @f f)
map_traverse :: (c ==> Wrap, Map t, c f) => (a -> f b) -> t a -> f (t b)
map_traverse f = pure < map (unwrap < f)
($@) :: Map f => (a -> b) -> f a -> f b
($@) = map
(!@) :: Map f => b -> f a -> f b
(!@) = mapConst

-- | Traverse over a container with a functor 
 {-forall cc. (cc ==> c) => Traverses cc t, c ==> Map_, -}
class (forall cc. (cc ==> c) => Traverses cc t, Map t) => Traverses c t where
  traverses :: c f => (a -> f b) -> t a -> f (t b)
  --traverses afb ta = sequenceC @c (map afb ta)
  sequenceC :: c f => t (f a) -> f (t a)
  sequenceC = traverses @c \ x -> x

type Fold = Traverses (Applicative & Comap)
type Fold1 = Traverses (Apply & Comap)

traverse :: (Traverses Applicative t,Applicative f) => (a -> f b) -> t a -> f (t b)
traverse = traverses @Applicative
sequence :: (Traverses Applicative t, Applicative f) => t (f a) -> f (t a)
sequence = sequenceC @Applicative

for, (@@) :: (Traverses Applicative t,Applicative f) => t a -> (a -> f b) -> f (t b)
for t f = traverses @Applicative f t
(@@) = for

traverse1 :: (Traverses Apply t,Apply f) => (a -> f b) -> t a -> f (t b)
traverse1 = traverses @Apply
for1 :: (Traverses Apply t,Apply f) => t a -> (a -> f b) -> f (t b)
for1 t = (`traverse1` t)
sequence1 :: (Traverses Apply t, Apply f) => t (f a) -> f (t a)
sequence1 = sequenceC @Apply

traverse0 :: (Traverses Pure t,Pure f) => (a -> f b) -> t a -> f (t b)
traverse0 = traverses @Pure
for0 :: (Traverses Pure t,Pure f) => t a -> (a -> f b) -> f (t b)
for0 t = (`traverse0` t)

traverse_ :: (Traverses Remap t,Remap f) => (a -> f b) -> t a -> f (t b)
traverse_ = traverses @Remap
for_ :: (Traverses Remap t,Remap f) => t a -> (a -> f b) -> f (t b)
for_ t = (`traverse_` t)

fold :: (Fold t, Scale0 m) => (a -> m) -> t a -> m
fold f = traverses @(Applicative & Comap) (f > K) > unK
(@.) :: (Traverses (Applicative & Comap) t, Scale0 m) => t a -> (a -> m) -> m
(@.) t = (`fold` t)

fold1 :: (Fold1 t, Scale0 m) => (a -> m) -> t a -> m
fold1 f = traverses @(Apply & Comap) (f > K) > unK

fold' :: (Traverses Applicative t, Op m) => (a -> m) -> t a -> E (t x) m
fold' f = swap < traverses @Applicative (L < f)

empty' :: Traverses Applicative t => t a -> Bool
empty' ta = case fold' (()!) ta of {L{} -> True; R{} -> False}
 
{-for_ :: forall c t a m. (Fold c t, c m) => t a -> (a -> m) -> m-}
{-for_ s am = foldMap @c am s-}


{-extract :: Traverses Constant f => f a -> a-}
{-extract = traverses @Constant K > unK-}

extract_traverse :: (Extract t, Constant f) => (a -> f b) -> t a -> f (t b)
extract_traverse afb (extract -> a) = comap extract (afb a)

extract0 :: (Traverses Pure f, Nil m) => (a -> m) -> f a -> m
extract0 f = traverses @Pure (f > K) > unK

(@?) :: (Traverses Pure t, Nil a) => t a -> a -> a
(@?) t a = usingInst (Reified_Nil a) do extract0 Instance t

newtype instance Reified Nil a = Reified_Nil a
instance Reifies s (Reified Nil a) => Nil (Instance Nil a s) where
  nil = let Reified_Nil a = reflect' @s
         in Instance @Nil a

-- | extract < remap f g = f < g < extract
class Traverses Constant w => Extract w where extract :: w a -> a

{-
 -newtype instance (Extract ## w) a = Extract (w a)
 -  deriving newtype Extract
 -  deriving (Remap, Map_) via Map ## Extract ## w
 -instance Extract w => Traverses Constant (Extract ## w) where
 -  traverses afb = constant < afb < extract
 -instance Extract w => Map (Extract ## w) where
 -  map f wa = _ $ traverses (K < f) wa
 -}


class Remap w => Duplicate w where
  {-extend :: (w a -> b) -> w a -> w b-}
  {-extend wab wa = remap (\_ -> wa) wab $ duplicate wa-}
  duplicate :: w a -> w (w a)
  {-duplicate = extend id-}
-- | extend extract = id
class (Extract w, Duplicate w) => Comonad w

-- * Monoidal Functors

-- | A @Monoidal@ functor over some associative monoidal product @t@
-- prop> remap (bimap f p) (bimap g q) (monoidal fa fb) = remap f g fa `monoidal` remap p q fb
class (Bimap t, Remap f) => Monoidal t f where monoidal :: f a -> f b -> f (a `t` b)
(|*|) :: Monoidal (,) f => f a -> f b -> f (a,b)
(|*|) = monoidal
(|+|) :: Monoidal E f => f a -> f b -> f (E a b)
(|+|) = monoidal
-- | A @Pure f@ is a pointed functor with a particular inhabited shape singled out
-- Free Theorem:
-- prop> pure < f = map f < pure
class ({- Lifting Scale0 One f, -} Remap f) => Pure f where
  {-# minimal pure | fone #-}
  pure :: a -> f a
  pure a = remap (()!) (a!) fone
  fone :: f ()
  fone = pure ()

class (Monoidal (,) f, Map f) => Apply f where
  ap :: f (a -> b) -> f a -> f b
  ap = liftA2 id
  liftA2 :: (a -> b -> c) -> f a -> f b -> f c
  liftA2 f = ap < map f
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

(|&|) :: Apply f => f a -> f (a -> b) -> f b
(|&|) = liftA2 (\a f -> f a)

newtype instance (Apply ## f) a = Apply (f a)
  deriving newtype (Apply,Map,Remap,Map_)
instance (Apply f, Op a) => Op ((Apply ## f) a) where op = liftA2 op

newtype instance (Pure ## f) a = Pure (f a) deriving newtype (Remap,Map_)
instance (Pure f, Nil a) => Nil ((Pure ## f) a) where nil = Pure $ pure nil

-- | prop> @pure f |$| fa@ = map f fa@
--   prop> ff |$| pure a = map ($ a) ff
class (Map f, Pure f, Apply f) => Applicative f
newtype instance (Applicative ## f) a = Applicative (f a)
  deriving newtype (Pure,Apply)
  deriving (Remap, Map_, Map#) via Map ## Applicative ## f
  deriving (Monoidal (,)) via Apply ## f
  deriving Op via (Apply ## f) a
  deriving Nil via (Pure ## f) a
instance Applicative f => Map (Applicative ## f) where map f = (pure f |$|)
instance Applicative f => P.Applicative (Applicative ## f) where
  pure = pure
  (<*>) = ap
instance (Applicative f, Scale0 a) => Scale0 ((Applicative ## f) a)
--instance (Applicative f, Rg a) => Rg ((Applicative ## f) a) where
  --(*) = coerce (liftA2 @f @a (*))
instance (c ==> Distribute, Map f) => Traverses c (Map ## f) where
  traverses afb (Map ta) = map_ Map < distribute @_ @f $ map @f afb ta
-- | distribute < imap (imap < iab) = imap (imap < flip iab) < distribute


class Distrib c t where distrib :: c f => f (t a) -> t (f a)
class Costrong w where costrong :: Pure f => w (f a) -> f (w a)
instance Costrong (E x) where
  costrong = \case
     L x -> pure (L x)
     R fa -> remap (\(R a) -> a) R fa

class Monad t => Distribute t where
  distribute :: Map f => f (t a) -> t (f a)
  distribute = collect \ x -> x
  zipWithF   :: Map f => (f a -> b) -> f (t a) -> t b
  zipWithF fab = \fta -> fab `map` distribute fta
  collect :: Map f => (a -> t b) -> f a -> t (f b)
  collect f a = zipWithF (\x -> x) (map f a)
newtype instance (Distribute ## t) a = Distribute (t a)
  deriving anyclass Applicative
  deriving (Remap, Map_) via Map ## Distribute ## t
instance Distribute t => Map (Distribute ## t) where
  map ab (Distribute ta) = Distribute $ zipWithF (unI > ab) (I ta)
instance Distribute t => Distribute (Distribute ## t) where
  distribute = Distribute < (map_ (\(Distribute ta) -> ta) > distribute)
  collect (coerce -> atb) = Distribute < collect atb
instance Distribute t => Pure (Distribute ## t) where
  pure = Distribute < map_ unK < distribute < K
instance Distribute t => Apply (Distribute ## t) where
  liftA2 f (Distribute ta) (Distribute tb) = Distribute
    $ zipWithF (\(V2 (L a) (R b)) -> f a b) (V2 (map L ta) (map R tb))
  Distribute tab `ap` Distribute ta = Distribute
    $ zipWithF (\(V2 (L f) (R a)) -> f a) (V2 (L $@ tab) (R $@ ta))
deriving via Apply ## Distribute ## t
  instance Distribute t => Monoidal (,) (Distribute ## t)
instance Distribute t => Monad (Distribute ## t) where
  bind atb ta = ta |&| distribute atb
instance Distribute t => MonadFix (Distribute ## t) where
  mfix = map fix < distribute

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
  deriving newtype Map
  deriving (Map_,Remap) via Map ## f
instance Empty f => FZero (Empty ## f) where fzero = Empty empty
instance Empty f => Nil ((Empty ## f) a) where nil = Empty empty

class (Append f, Empty f) => Alternative f

-- | (fa ++ fb) `monoidal` fc = (fa `monoidal` fc) ++ (fb `monoidal` fc)
{-instance (Rg1 f, Op a) => Rg ((Rg1 ## f) a) where (*) = liftA2 (.)-}

-- | Covariant E-monoidal functors can be appended
class (forall x. Op (f x), Monoidal E f, Map f) => Append f where
  (|.|) :: f a -> f a -> f a
  (|.|) fa fa' = map (\case L a -> a; R b -> b) (fa `monoidal` fa')
newtype instance (Append ## f) a = Append (f a)
  deriving newtype Map
  deriving (Map_,Remap) via Map ## f
instance Append f => Monoidal E (Append ## f) where
  monoidal (Append fa) (Append fb) = Append $ map L fa |.| map R fb
instance Append f => Op ((Append ## f) a) where Append f `op` Append g = Append (g |.| f)
append a = (|.| a)

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

class (Map f, Comap f, Representational f) => Constant f where
  constant :: f a -> f b
  constant = map absurd < comap absurd
instance {-# overlappable #-} (Map f, Comap f, Representational f) => Constant f

-- * Monads
class Applicative m => Monad m where bind :: (a -> m b) -> m a -> m b
newtype instance (Monad ## m) a = Monad (m a)
  deriving newtype (Monad, Applicative, Pure)
  deriving (Monoidal (,), Remap, Map, Map_) via Applicative ## Monad ## m
instance Monad m => Apply (Monad ## m) where
  Monad mab `ap` Monad ma = Monad (mab >>= \ ab -> ma >>= (ab $) > pure)
instance Monad m => Bound m (Monad ## m) where bound f (Monad m) = Monad $ bind f m
(=<<) :: Monad m => (a -> m b) -> m a -> m b
(=<<) = bind
(>=>) :: Monad m => (a -> m b) -> (b -> m c) -> a -> m c
f >=> g = \a -> f a >>= g
(>>=) :: Monad m => m a -> (a -> m b) -> m b
(>>=) m = (=<< m)
infixl 1 >>=
infixr 1 =<<, >=>

class Monad m => MonadFix m where mfix :: (a -> m a) -> m a
-- | imap f . imap g = imap (\i -> f i . g i)
--   imap (\_ -> f) = map f

-- | @f@ is a Monad-Module over @m@
class (Monad m, Map f) => Bound m f where
  bound :: (a -> m b) -> f a -> f b
  joined :: f (m a) -> f a
  joined = bound id
  filter :: m ~ Maybe => (a -> Bool) -> f a -> f a
  filter f = bound \ a -> case f a of {False -> Nothing; True -> Just a}
  partition :: m ~ Maybe => (a -> Bool) -> f a -> (f a, f a)
  partition f fa = (filter f fa, filter (P.not < f) fa)

class (Bound Maybe f, Monoidal These f) => Align f where
  {-zip :: f a -> f b -> f (a,b)-}
  {-zip fa fb = fmap (\case These a b -> Just (a,b); _ -> Nothing) $ align fa fb-}
  alignWith :: (a -> c) -> (b -> c) -> (a -> b -> c) -> f a -> f b -> f c
  alignWith f g h = \a b -> go $@ monoidal @These a b where
    go = \case
      This x -> f x
      That y -> g y
      These x y -> h x y
newtype instance (Align ## f) a = Align (f a)
{-instance Align f => Monoidal These (Align ## f) where-}
  {-monoidal = coerce (alignWith @f This That These)-}
align :: Monoidal These f => f a -> f b -> f (These a b)
align = monoidal @These

class (LMap f, forall x. Map (f x)) => Bimap f where
  bimap :: (x -> a) -> (y -> b) -> f x y -> f a b
newtype instance (Bimap ### f) a b = Bimap (f a b)
  deriving newtype Bimap
  deriving (Remap,Map_) via Map ## (Bimap ### f) a
instance Bimap f => Map ((Bimap ### f) a) where map f (Bimap fab) = Bimap (bimap id f fab)
instance Bimap f => LMap (Bimap ### f) where lmap = (`bimap` id)

class LMap f where lmap :: (a -> b) -> f a x -> f b x

-- * Coercions
class    ((forall a b. a =# b => f a =# f b)) => Representational f
instance ((forall a b. a =# b => f a =# f b)) => Representational f
newtype instance (Representational ## f) a = Representational (f a)
instance Representational f => Map_ (Representational ## f) where mapAs = coerce
representational :: forall b a f. (a =# b, Representational f) => f a -> f b
representational = GHC.coerce
{-# INLINE representational #-}

-- | 'Phantom' types can ignore their type parameter. Instances are automatically provided by GHC
class    (forall x y. f x =# f y) => Phantom f
instance (forall x y. f x =# f y) => Phantom f
newtype instance (Phantom ## f) a = Phantom (f a)
instance Phantom f => Map (Phantom ## f) where map _ = coerce
instance Phantom f => Remap (Phantom ## f) where remap _ _ = coerce
instance Phantom f => Comap (Phantom ## f) where comap _ = coerce
instance Phantom f => Map_ (Phantom ## f) where mapAs = coerce
instance Phantom f => Constant (Phantom ## f) where constant = coerce
instance (Phantom f, Append f, Bimap t) => Monoidal t (Phantom ## f) where
  Phantom fa `monoidal` Phantom fb = Phantom < phantom $ fa |.| phantom fb
instance (Phantom f, Append f) => Apply (Phantom ## f) where
  Phantom fab `ap` Phantom fa = Phantom < phantom $ fab |.| phantom fa
instance (Phantom f, Empty f) => Pure (Phantom ## f) where pure _ = Phantom empty
instance (Alternative f, Phantom f) => Applicative (Phantom ## f)
instance (Alternative m, Phantom m) => Monad (Phantom ## m) where bind _ = coerce
phantom_traverses :: (c ==> Pure, c f, Phantom t) => (a -> f b) -> t a -> f (t b)
phantom_traverses _ = pure < phantom
-- Doesn't actually work because deriving via can't get under @f@, use above instead
instance (Phantom f, c ==> Pure) => Traverses c (Phantom ## f) where
  traverses _ (Phantom k) = (pure < Phantom < phantom) k
phantom :: forall b a f. Phantom f => f a -> f b
phantom = GHC.coerce @(f a) @(f b)

-- | @Wrap@ed functors are (representationally) isomorphic to identity
class (Distribute f
      --,forall c. c ==> Map => Traverses c f
      ,Representational f
      ,forall x. x =# f x
      ,Map f
      ,Extract f) => Wrap f
instance (Distribute f
        --,forall c. c ==> Map => Traverses c f
        ,Representational f
        ,forall x. x =# f x
        ,Map f
        ,Extract f) => Wrap f
newtype instance (Wrap ## f) a = Wrap (f a)
instance Wrap f => Monad (Wrap ## f) where bind = coerce
instance Wrap f => Distribute (Wrap ## f) where distribute = pure < map_ unwrap
instance Wrap f => Extract (Wrap ## f) where extract = unwrap
deriving via Representational ## f instance Wrap f => Map_ (Wrap ## f)
instance Wrap f => Map (Wrap ## f) where map = coerce
instance Wrap f => Remap (Wrap ## f) where remap _ = coerce
instance Wrap f => Applicative  (Wrap ## f)
instance Wrap f => Pure (Wrap ## f) where pure = coerce
instance Wrap f => Apply (Wrap ## f) where ap = unwrap > coerce
instance Wrap f => Monoidal (,) (Wrap ## f) where
  monoidal (unwrap -> a) (unwrap -> b) = pure (a,b)
wrap_traverses :: (c ==> Map_, c f, Wrap t) => (a -> f b) -> t a -> f (t b)
wrap_traverses f (unwrap -> a) = map_ pure $ f a
instance (Wrap f, c ==> Map_) => Traverses c (Wrap ## f) where
  traverses f (Wrap (unwrap -> a)) = map_ pure $ f a
unwrap :: Wrap f => f a -> a
unwrap = coerce

-- | Strictly map a coercion over a functor, 
-- using 'coerce' if it's 'Representational' or `remap` otherwise.
class Map_ f where mapAs :: b =# a => f a -> f b
map_ :: forall f a b. (Map_ f, a =# b) => (a -> b) -> f a -> f b
map_ _ = mapAs @f @b @a
comap_ :: forall f a b. (Map_ f, a =# b) => (b -> a) -> f a -> f b
comap_ _ = mapAs @f @b @a
(#@) :: (Map_ f, a =# b) => (a -> b) -> f a -> f b
(#@) = map_

type family LeftF t where LeftF (E a) = a
class (Map f, f ~ E (LeftF f)) => IsEither f
instance IsEither (E a)

newtype Threader i a = Threader (i -> (i,a))
  deriving stock Map# deriving Map via Map# ## Threader i
  deriving Remap via Map ## Threader i
  deriving Map_ via Representational ## Threader i
instance Pure (Threader i) where pure a = Threader \ i -> (i,a)
{-instance Apply (Threader i) where -}

data Store i a = Store i (i -> a)
pos (Store i _) = i
eval (Store i ia) = ia i

{-imap :: (P.Enum i, Traverses Applicative f) => (i -> a -> b) -> f a -> f b-}
{-imap iab fa = traverses (\-}


-- Instances --

-- Stock
type Map# = P.Functor
newtype instance (Map# ## f) a = Map# (f a)
  deriving newtype Map#
  deriving (Remap, Map_) via Map ## Map# ## f

type Applicative# = P.Applicative
newtype instance (Applicative# ## f) a = Applicative# (f a)
  deriving newtype (Map#, Applicative#)
  deriving (Remap,Map,Map_) via Map# ## f
  deriving (Monoidal (,)) via Apply ## Applicative# ## f
instance Applicative# f => Pure (Applicative# ## f) where pure = P.pure
instance Applicative# f => Apply (Applicative# ## f) where ap = (P.<*>)
instance Applicative# f => Applicative (Applicative# ## f)

type Monad# = P.Monad
newtype instance (Monad# ## m) a = Monad# (m a)
  deriving newtype (Monad#,Applicative#,Map#)
  deriving (Applicative,Apply,Monoidal (,),Pure,Remap,Map,Map_) via Applicative# ## m

type Fold# = P.Foldable
newtype instance (Fold# ## f) a = Fold# (f a)
  deriving newtype (Fold#,Map#)
  deriving (Remap,Map,Map_) via Map# ## f

type Traverse# = P.Traversable
newtype instance (Traverse# ## f) a = Traverse# (f a)
  deriving newtype Map#
  deriving (Remap,Map,Map_) via Map# ## f
instance Fold# f => P.Foldable (Traverse# ## f) where -- TODO: fix
  foldMap f (Traverse# tm) = P.foldMap f tm


instance Traverse# f => P.Traversable (Traverse# ## f) where -- TODO: fix
  traverse f (Traverse# tm) = coerce# (P.traverse f tm)

type MonadFix# = P.MonadFix
newtype instance (MonadFix# ## m) a = MonadFix# (m a)
  deriving newtype (Monad#, Applicative#, Map#, MonadFix#)
  deriving (Monad,Applicative,Apply,Monoidal (,),Pure,Map,Remap,Map_) via Monad# ## m


newtype instance (Stock ## f) a = Stock1 (f a)
  deriving newtype (P.Functor,P.Foldable,P.Applicative, P.Monad)
instance P.Traversable f => P.Traversable (Stock ## f) where
  traverse afb (Stock1 ta) = P.fmap Stock1 (P.traverse afb ta)

instance P.Monad f => Monad (Monad# ## f) where bind f = (P.>>= f)
instance (c ==> Applicative, Traverse# f) => Traverses c (Traverse# ## f) where
  traverses afb (Traverse# ta) = map_ Traverse# < (\(Applicative x) -> x)
                            $ P.traverse (Applicative < afb) ta
instance Map# f => Map (Map# ## f) where map = P.fmap
instance MonadFix# m => MonadFix (MonadFix# ## m) where mfix = MonadFix# < P.mfix < coerce


data V2 a = V2 {v2a :: a, v2b :: a}
  deriving stock (Map#, P.Traversable, P.Foldable)
  deriving (Remap,Map) via Map# ## V2
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
instance c ==> Pure => Traverses c Maybe where
  traverses f = \case
    Nothing -> pure Nothing
    Just a -> remap (\case Just a -> a) Just $ f a
{-instance Align Maybe where-}
  {-alignWith this that these = go where-}
    {-go Nothing Nothing = Nothing-}
    {-go (Just a) Nothing = Just (this a)-}
    {-go Nothing (Just b) = Just (that b)-}
    {-go (Just a) (Just b) = Just (these a b)-}

-- E
deriving via Representational ## E x instance Map_ (E x)
instance Bimap E where bimap f g = \case {L a -> L $ f a; R b -> R $ g b}
deriving via ((Bimap ### E) a) instance Map (E a)
deriving via ((Bimap ### E) a) instance Remap (E a)
deriving via Bimap ### E instance LMap E
instance Pure (E x)   where pure = R
deriving via Apply ## (E x) instance Op x => Monoidal (,) (E x)
instance Op x => Apply (E x) where
  ap (R f) (R a) = R (f a)
  ap (L x) (R _) = L x
  ap (R _) (L y) = L y
  ap (L x) (L y) = L (y . x)
instance Op x => Applicative (E x)


instance c ==> Pure => Traverses c (E x) where
  traverses afb = \case {L x -> pure (L x); R a -> remap (\case R a -> a) R (afb a)}

-- (->)
type Reader = (->)
instance Map (Reader x) where map f g = \a ->  f (g a)
deriving via Map ## Reader x instance Remap (Reader x)
deriving via Representational ## Reader x instance Map_ ((->) x)
instance Distribute (Reader x) where distribute fxa x = map ($ x) fxa
instance Pure (Reader x) where pure = (!)
instance Apply (Reader x) where ap iab ia = \i -> iab i $ ia i
deriving via Apply ## (Reader x) instance Monoidal (,) ((->) x)
instance Applicative (Reader x)
instance Monad (Reader x) where bind aib ia = \i -> aib (ia i) i
{-deriving via Apply ## ((->) x) instance Op a => Op (x -> a)-}
instance (Nil x, c ==> Remap) => Traverses c (Reader x) where
  traverses afb xa = remap ($ nil) (\b _ -> b) (afb (xa nil))

instance Nil x => Extract ((->) x) where extract f = f nil
instance Op x => Duplicate ((->) x) where duplicate f x = \x' -> f (op x x') -- TODO: cherck order
instance Scale0 x => Comonad ((->) x)

newtype Re b a = Re {runRe :: a -> b}
  deriving (Map_, Remap) via Comap ## Re b

instance Comap (Re s) where f `comap` Re g = Re $ f > g
deriving via (Applicative ## ((->) a)) s instance Op s => Op (Re s a)
deriving via (Applicative ## ((->) a)) s instance Nil s => Nil (Re s a)
deriving via (Applicative ## ((->) a)) s instance Scale0 s => Scale0 (Re s a)

deriving via Representational ## Endo instance Map_ Endo
instance Remap Endo where remap ba ab (Endo aa) = Endo $ ba > aa > ab
instance Bimap t => Monoidal t Endo where monoidal (Endo f) (Endo g) = Endo $ bimap f g

-- []
deriving via Empty            ## [] instance FZero []
deriving via Representational ## [] instance Map_ []
instance Empty [] where empty = []
deriving via (Empty ## []) a instance Nil [a]
instance Scale0 [a]
deriving via Map ## [] instance Remap []
instance Map   [] where map = P.map
instance Pure  [] where pure a = [a]
instance Append [] where (|.|) = (P.++) -- TODO: fix
deriving via (Append ## []) a instance Op [a]
deriving via Append ## [] instance Monoidal E []
instance Apply [] where ap = (P.<*>) -- TODO: fix
instance Applicative []
deriving via Apply ## [] instance Monoidal (,) []
{-deriving via (Rg1 ## []) a instance Op a => Rg [a]-}
instance (c ==> Applicative) => Traverses c [] where
  traverses f = go where
    go = \case
      [] -> pure []
      a : as -> (:) $@ f a |$| go as
instance Bound Maybe [] where
  bound f = go where
    go [] = []
    go ((f -> Nothing):as)  =     go as
    go ((f -> Just b) :as)  = b : go as
  filter = P.filter
{-instance Align [] where-}
  {-alignWith this that these = go where-}
      {-go [] bs = that $@ bs-}
      {-go as [] = this $@ as-}
      {-go (a:as) (b:bs) = these a b : go as bs-}

instance Bimap These where
  bimap f g = \case
    This a -> This $ f a
    That b -> That $ g b
    These a b -> f a `These` g b
deriving via (Bimap ### These) a instance Map   (These a)
deriving via (Bimap ### These) a instance Remap (These a)
deriving via  Bimap ### These    instance LMap   These
deriving via (Representational ## These a) instance Map_ (These a)

-- (,)
type Writer = (,)
deriving via Representational ## (,) x instance Map_ (Writer x)
deriving via Map ## Writer x instance Remap (Writer x)
instance Map  (Writer x) where map f (x,a)     = (  x, f a)
instance Bimap Writer    where bimap f g (a,b) = (f a, g b)
instance LMap  Writer    where lmap f (a,x)    = (f a,   x)
instance c ==> Remap => Traverses c (Writer x) 
  where traverses f (x,a) = remap (\(_,b) -> b) (x,) (f a)

-- I
deriving via Wrap ## I instance Pure I
deriving via Wrap ## I instance Apply I
deriving via Wrap ## I instance Monoidal (,) I
deriving via Wrap ## I instance Monad I
deriving via Wrap ## I instance Map I
deriving via Wrap ## I instance Remap I
deriving via Wrap ## I instance Extract I
instance Applicative I
deriving via Wrap ## I instance Map_ I
instance c ==> Map_ => Traverses c I where traverses f (I a) = map_ I (f a)
instance Distribute I where distribute (fia :: f (I a)) = I (map_ unI fia)

-- K
deriving via Phantom ## K a instance Map (K a)
deriving via Phantom ## K a instance Remap (K a)
deriving via Phantom ## K a instance Comap (K a)
deriving via Phantom ## K a instance Map_ (K a)
instance c ==> Pure => Traverses c (K a) where traverses = phantom_traverses @c
instance Nil a => Empty (K a) where empty = K nil
deriving via Empty ## K a instance Nil a => FZero (K a)
instance Op a => Append (K a) where K a |.| K b = K $ op b a -- TODO: fix
deriving via Append ## K a instance Op a => Monoidal E (K a)
instance Scale0 a => Alternative (K a)
deriving via (Append ## K a) x instance Op a => Op (K a x)
deriving via Phantom ## K a instance Op a => Apply (K a)
deriving via Phantom ## K a instance Op a => Monoidal (,) (K a)
deriving via Phantom ## K a instance Nil a => Pure (K a)
instance Scale0 a => Applicative (K a)
instance Scale0 a => Distribute (K a) where distribute _ = K nil
deriving via Phantom ## K a instance Scale0 a => Monad (K a)

-- IO
instance Monad P.IO where bind f io = io P.>>= f
instance Applicative P.IO
instance Apply P.IO where ap = (P.<*>)
deriving via Apply ## P.IO instance Monoidal (,) P.IO
instance Pure P.IO where pure = P.pure
instance Map P.IO where map = P.fmap
deriving via Representational ## P.IO instance Map_ P.IO
deriving via Map ## P.IO instance Remap P.IO

deriving via (Apply ## P.IO) a instance Op a => Op (P.IO a)
deriving via (Pure ## P.IO) a instance Nil a => Nil (P.IO a)
deriving via (Applicative ## P.IO) a instance Scale0 a => Scale0 (P.IO a)

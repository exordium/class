{-# language TemplateHaskell,QuasiQuotes #-}
{-# language MagicHash #-}
{-# language EmptyCase #-}
{-# language UndecidableSuperClasses #-}
{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language InstanceSigs #-}
{-# language UndecidableInstances #-}
module Control where
import GHC.Types
import Impl hiding ((!))
import TV
import qualified Prelude as P
import Type.Bazaar
import Type.E
import Type.I
import Type.O
import Type.K
import Type.X
import Unsafe.Coerce
import Data.Proxy
import Types
import Fun
import Data
import qualified Data.Coerce as GHC
import qualified Control.Arrow as P
import qualified Control.Category as P
import Functor hiding ((|||))

class Compose p where compose :: p a b -> p b c -> p a c
class Identity p where identity :: p a a
class (Compose p, Identity p) => Category p
(>>>) :: Compose p => p a b -> p b c -> p a c
(>>>) = compose
(<<<) :: Compose p => p b c -> p a b -> p a c
p <<< q = compose q p

class (Category p, Promap p) => Arr p where
  arr :: (a -> b) -> p a b
  arr f = f ^> identity
class (Arr p, Lensed p) => Arrow p where
  (***) :: p x a -> p y b -> p (x,y) (a,b)
  p *** q = _1 p >>> _2 q
  (&&&) :: p x a -> p x b -> p x (a,b)
  p &&& q = (\a -> (a,a)) ^> (p *** q)
class (Arr p, Prismed p) => ArrowChoice p  where
  (+++) :: p x a -> p y b -> p (E x y) (E a b)
  p +++ q = _L p >>> _R q
  (|||) :: p x a -> p y a -> p (E x y) a
  p ||| q =  (p +++ q) >^ (\case L a -> a; R a -> a)


-- * Promap
class (forall x. MapRep (p x)) => PromapRep p where
  {-# minimal promapRep | premapRep,postmapRep #-}
  promapRep :: (s =# a, b =# t) => (s -> a) -> (b -> t) -> p a b -> p s t
  promapRep f g = premapRep f > postmapRep g
  premapRep :: (s =# a) => (s -> a) -> p a t -> p s t
  premapRep = (`promapRep` \ t -> t)
  postmapRep :: (b =# t) => (b -> t) -> p s b -> p s t
  postmapRep = promapRep \ s -> s

class (forall x. Map (p x), PromapRep p) => Promap p where
  {-# minimal promap | premap,postmap #-}
  promap  :: (s -> a) -> (b -> t) -> p a b -> p s t
  promap f g = premap f > postmap g
  premap  :: (s -> a) -> p a t -> p s t
  premap = (`promap` \ t -> t)
  postmap :: (b -> t) -> p s b -> p s t
  postmap =  promap  \ s -> s

-- * Closed
class Promap p => Closed p where
  distributed :: forall t a b. Distribute t => p a b -> p (t a) (t b)
  distributed = zipping zipWithF
  closed :: p a b -> p (x -> a) (x -> b)
  closed = distributed
  grate :: (((s -> a) -> b) -> t) -> p a b -> p s t
  grate sa_b_t = \ab -> promap (\a g -> g a) sa_b_t (distributed ab)
  zipping :: (forall f. Map f => (f a -> b) -> f s -> t) -> p a b -> p s t
  zipping sabsst = grate (`sabsst` \ s -> s)

type Fold c = TraverseC (IsK c)

foldMap :: forall c t a m. (Fold c t, c m) => (a -> m) -> t a -> m
foldMap am = unK < traverseC @(IsK c) (K < am)

for_ :: forall c t a m. (Fold c t, c m) => t a -> (a -> m) -> m
for_ s am = foldMap @c am s

{-(./) :: (Fold Add0 t, Add0 m) => t a -> (a -> m) -> m-}
{-(./) = for_ @Add0-}
{-(+/) :: (Fold Add0 t, Add0 m) => t a -> (a -> m) -> m-}
{-(+/) = for_ @Add0-}
{-(*/) :: (Fold Mul1 t, Mul1 m) => t a -> (a -> m) -> m-}
{-(*/) = for_ @Mul1-}


cocollect :: forall c f t a b. (TraverseC c t, c ==> Map, c f)
          => (t a -> b) -> t (f a) -> f b
cocollect tab tfa = map tab (sequence @c tfa)

type Mapped = TraversedC (Applicative & Distribute)

class (Promap p, forall cc. (c ==> cc) => TraversedC cc p)
  => TraversedC (c :: (* -> *) -> Constraint) p where
  traversedC :: TraverseC c t => p a b -> p (t a) (t b)
  traversedC = traversalC @c (traverseC @c)
  traversalC :: (forall f. c f => (a -> f b) -> s -> f t) -> p a b -> p s t
  {-default traversalC :: (forall ff bb aa. c ff => c (O ff (Bazaar c bb aa))-}
                       {-,c I , c (Baz c t b))-}
                    {-=> (forall f. c f => (a -> f b) -> s -> f t)-}
                    {--> p a b -> p s t-}
  {-traversalC f pab = promap (\s -> Baz (\afb -> f afb s)) (sold @c) (traversedC @c pab)-}

class TraversedC Map p => Lensed p where
  lens :: (s -> a) -> (s -> b -> t) -> p a b -> p s t
  lens get set = traversalC @Map \ afb s -> set s `map` afb (get s)
  _2 :: p a b -> p (x,a) (x,b)
  _2 = traversedC @Map
  _1 :: p a b -> p (a,x) (b,x)
  _1 p = let swap (a,b) = (b,a) in promap swap swap (_2 p)

folding :: forall c p a s b t. TraversedC (IsK c) p
        => (forall m. c m => (a -> m) -> s -> m) -> p a b -> p s t
folding amsm = traversalC @(IsK c) (\akm s -> K (amsm (unK < akm) s))

lens0 :: (Prismed p, Lensed p) => (s -> E t a) -> (s -> b -> t) -> p a b -> p s t
lens0 get set pab = promap (\s -> (get s, s)) (\(bt,s) -> case bt of {L t -> t; R b -> set s b}) (_1 (_R pab))

-- | 'Closed' over @(~) (E x))@
class Promap p => Prismed p where
  {-# minimal prism | _R #-}
  prism :: (s -> E t a) -> (b -> t) -> p a b -> p s t
  prism pat constr = promap pat (id ||| constr) < _R
  _R ::  p a b -> p (E x a) (E x b)
  _R = prism (\case L t -> L (L t); R a -> R a) R
  _L :: p a b -> p (E a y) (E b y)
  _L = promap swap swap < _R

class Prismed p => Precoerce p where
  {-# minimal from | precoerce #-}
  from :: (b -> t) -> p a b -> p s t
  from bt p = precoerce (postmap bt p)
  precoerce :: p a x -> p s x
  precoerce = from \ x -> x

class ((forall x y a b . (a =# x,y =# b) => p x y =# p a b),PromapRep p) => Representational2 p
instance ((forall x y a b . (a =# x,y =# b) => p x y =# p a b), PromapRep p)=> Representational2 p

class (Applicative f, Distribute f) => IsI f
instance (Applicative f, Distribute f) => IsI f

-- * Instances

instance Promap (->) where
  promap  = \f g p s -> g (p (f s))
  premap  = \f p s -> p (f s)
  postmap = \g p a -> g (p a)
instance PromapRep (->) where promapRep _ _ = coerce
instance Closed  (->)     where distributed = map; closed f = (f <)
instance (((~) I) ==> c) => TraversedC c (->) where
 traversedC = map
 traversalC l f s = case l (\a -> I (f a)) s of {I t -> t} 
instance Prismed (->) where _R ab = \case {L x -> L x; R a -> R (ab a)}
instance Lensed (->)
instance Compose (->) where compose = (>)
instance Identity (->) where identity = id
instance Category (->)



deriving via (Representational ## Baz c t b) instance MapRep (Baz c t b)
deriving via (Map ## Baz c t b) instance Remap (Baz c t b)
instance Map (Baz c t b) where
  map xy (Baz xfbft) = Baz \ yfb -> xfbft \ x -> yfb (xy x)
class (Map f, Comap f) => IsKK f
instance  (Map f, Comap f) => IsKK f

{-instance (forall f x. c (O f (Bazaar c x b)), forall x. c (K x), c ==> Remap)-}
instance (forall f x. c (O f (Bazaar c x b)), forall x. c (K x), c ==> Remap)
  => TraverseC c (Baz c t b) where
     traverseC f (Baz bz) = mapRep Baz_ (unO (bz (\x -> O (remap buy (sell @c) (f x)))))

data A; data B
class C a

instance (c ==> Map, c (Bazaar c a b)) => Map (Bazaar c a b) where
  map f (Bazaar m) = Bazaar (\afb -> map f (m afb))
  {-map f (Bazaar m) = Bazaar (map f < m)-}
instance c ==> MapRep => MapRep (Bazaar c a b)
  where mapRep f (Bazaar m) = Bazaar (mapRep f < m)
instance c ==> Remap => Remap (Bazaar c a b) where
  remap f g (Bazaar m) = Bazaar (\k -> remap f g (m k))
instance (c (Bazaar c a b), c ==> Pure) => Pure (Bazaar c a b) where
  pure t = Bazaar (pure t!)

instance (c (Bazaar c a b), c ==> Apply) => Apply (Bazaar c a b) where
  ap (Bazaar afbfxy) (Bazaar afbfx) = Bazaar \ afb -> afbfxy afb `ap` afbfx afb
instance (c (Bazaar c a b), c ==> Applicative) => Applicative (Bazaar c a b)
instance (c (Bazaar c a b), c ==> Monad) => Monad (Bazaar c a b) where
  bind abz (Bazaar xmyma) = Bazaar \ xmy ->
    (`bind` xmyma xmy) \ a -> case abz a of Bazaar xmymb -> xmymb xmy

{-instance (c (Bazaar c a b), c ==> Monad) => Monad (Bazaar c a b) where-}
  {-traverseC afb (Bazaar agyga) = -}

    


{-instance {-# Overlappable #-} Promap p => PromapRep p where-}
  {-promapRep _ _ !p = promap coerce coerce p-}
-- |A @Pure f@ distributes through Sum types:
--  http://r6research.livejournal.com/28338.html
{-instance {-# Overlappable #-} (Pure t, Zero x) => One (t x) where one = pure zero-}


type family Left t where Left (E a b) = a
type family Right t where Right (E a b) = b
class a ~ E (Left a) (Right a) => IsEither' a
instance a ~ E (Left a) (Right a) => IsEither' a


instance {-# overlappable #-} (Category p, Promap p) => Arr p
instance {-# overlappable #-} (Arr p, Lensed p) => Arrow p
instance {-# overlappable #-} (Arr p, Prismed p) => ArrowChoice p
instance {-# overlappable #-} Category p => P.Category p
  where p . q = compose q p; id = identity
instance {-# overlappable #-} Arrow p => P.Arrow p
  where arr = arr; (***) = (***); (&&&) = (&&&)
instance {-# overlappable #-} (Arrow p, ArrowChoice p) => P.ArrowChoice p where
  p +++ q = either2e ^> (p +++ q) >^ e2either
    where e2either = \case L a -> P.Left a; R b -> P.Right b
          either2e = \case P.Left a -> L a; P.Right b -> R b
  p ||| q = either2e ^> (p ||| q)
    where either2e = \case P.Left a -> L a; P.Right b -> R b

-- * Ops

(^>) :: Promap p => (s -> a) -> p a x -> p s x
(^>) = premap
p <^ f = premap f p
p >^ f = postmap f p
(^<) :: Promap p => (b -> t) -> p x b -> p x t
(^<) = postmap

data family (###) (c :: (* -> * -> *) -> Constraint) :: (* -> * -> *) -> * -> * -> *

newtype instance (Promap ### p) a b = Promap (p a b)
  deriving newtype Promap
  deriving (Remap,MapRep) via (Promap ### p) a
instance Promap p => Map ((Promap ### p) a) where map f (Promap p) = Promap (postmap f p)
instance Promap p => PromapRep (Promap ### p) where
  promapRep _ _ !p = promap coerce coerce p
  premapRep _ !p = premap coerce p
  postmapRep _ !p = postmap coerce p

newtype instance (PromapRep ### p) a b = PromapRep (p a b)
  deriving newtype PromapRep
instance PromapRep p => MapRep ((PromapRep ### p) a) where
  mapRep f (PromapRep p) = PromapRep (postmapRep f p)

newtype instance (Representational2 ### p) a b = Representational2 (p a b)
  deriving MapRep via (PromapRep ### p) a
instance Representational2 p => PromapRep (Representational2 ### p)
  where promapRep  _ _ = coerce

{-newtype Ar a b = Ar (a -> b)-}
  {-deriving newtype (Promap, PromapRep, MapRep)-}
  {-deriving (Map) via Promap ### Ar a-}




{-instance Bind I (Baz c t b) where bind = map_bind-}
{-deriving via (Promap ### (Baz c t) b) instance Promap (Baz c t) => Bind I (Baz c t b)-}


{-instance Impl Promap where-}
  {-type Methods Promap = '[Required "promap"]-}
  {-impl p (Arg promap) = [d|-}
    {-instance Promap  $p where promap   = $promap-}
    {-instance Premap  $p where premap f = $promap f \ x -> x-}
    {-instance Postmap $p where postmap  = $promap \ x -> x-}
    {-instance Map    ($p [tv|x|]) where map      = postmap-}
    {-instance TraverseC IsI ($p [tv|x|]) where traverseC = map_traverseC-}
    {-instance Strong ($p [tv|x|]) where strong a = map ((,) a)-}
    {-instance Remap  ($p [tv|x|]) where remap _  = map-}
    {-instance MapRep  ($p [tv|x|]) where mapRep = remap_mapRep-}
   {-|]-}

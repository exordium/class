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
import qualified Prelude as P
import Type.Bazaar
import Type.E
import Type.I
import Type.K
import Type.X
import Unsafe.Coerce
import Data.Proxy
import Types
import Fun
import Data
import qualified Data.Coerce as GHC
import qualified Control.Arrow as P
import qualified Control.Category as PC
import Functor hiding ((|||))

class Compose p where compose :: p a b -> p b c -> p a c
class Identity p where identity :: p a a
class (Compose p, Identity p) => Category p
(>>>) :: Compose p => p a b -> p b c -> p a c
(>>>) = compose
(<<<) :: Compose p => p b c -> p a b -> p a c
p <<< q = compose q p

-- | @p@ has a homomorphic embedding from @Hask@
-- 
-- prop> promap f g p = arr f >>> p >>> arr g
-- prop> arr (f > g) = arr f >>> arr g
-- prop> arr id = identity
class (Category p, Promap p) => Arr p where
  arr :: (a -> b) -> p a b
  arr = (identity ^>)
class (Arr p, Traversed Map p) => Arrow p where
  (***) :: p x a -> p y b -> p (x,y) (a,b)
  p *** q = _1 p >>> _2 q
  (&&&) :: p x a -> p x b -> p x (a,b)
  p &&& q =  p *** q ^< \ a -> (a,a)
class (Arr p, Prismed p) => ArrowChoice p  where
  (+++) :: p x a -> p y b -> p (E x y) (E a b)
  p +++ q = _L p >>> _R q
  (|||) :: p x a -> p y a -> p (E x y) a
  p ||| q =  p +++ q ^> (\case L a -> a; R a -> a)


newtype EndoP p a = EndoP (p a a)
instance Promap p => Remap (EndoP p) where remap f g (EndoP p) = EndoP $ promap f g p
instance Promap_ p => Map_ (EndoP p) where map_ _ (EndoP p) = EndoP $ promap_ coerce coerce p
{-instance ArrowChoice \c -}

infixl 2 |||, +++
infixl 3 &&&, ***


-- * Promap
class (forall x. Map_ (p x)) => Promap_ p where
  {-# minimal promap_ | premap_,postmap_ #-}
  promap_ :: (s =# a, b =# t) => (s -> a) -> (b -> t) -> p a b -> p s t
  promap_ f g = premap_ f > postmap_ g
  premap_ :: (s =# a) => (s -> a) -> p a t -> p s t
  premap_ = (`promap_` \ t -> t)
  postmap_ :: (b =# t) => (b -> t) -> p s b -> p s t
  postmap_ = promap_ \ s -> s

class (forall x. Map (p x), Promap_ p) => Promap p where
  {-# minimal promap | premap,postmap #-}
  promap  :: (s -> a) -> (b -> t) -> p a b -> p s t
  promap f g = premap f > postmap g
  premap  :: (s -> a) -> p a t -> p s t
  premap = (`promap` \ t -> t)
  postmap :: (b -> t) -> p s b -> p s t
  postmap =  promap  \ s -> s

(>^<) :: Promap p => (s -> a) -> (b -> t) -> p a b -> p s t
(>^<) = promap
infixr 1 >^<, ^>, ^<, >^, <^
(>^) :: Promap p => (s -> a) -> p a x -> p s x
(>^) = premap
p ^< f = premap f p
p ^> f = postmap f p
(<^) :: Promap p => (b -> t) -> p x b -> p x t
(<^) = postmap

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

{-(./) :: (Fold Add0 t, Add0 m) => t a -> (a -> m) -> m-}
{-(./) = for_ @Add0-}
{-(+/) :: (Fold Add0 t, Add0 m) => t a -> (a -> m) -> m-}
{-(+/) = for_ @Add0-}
{-(*/) :: (Fold Mul1 t, Mul1 m) => t a -> (a -> m) -> m-}
{-(*/) = for_ @Mul1-}


cocollect :: forall f t a b. (Traverses Map t, Map f)
          => (t a -> b) -> t (f a) -> f b
cocollect tab tfa = map tab (sequenceC @Map tfa)

type Mapped p = Traversed Wrap p
type Lensed p = Traversed Map p

class Promap p => Traversed c p | p -> c where
  traversed :: Traverses c t => p a b -> p (t a) (t b)
  traversed = traversal (traverses @c)
  traversal :: (forall f. c f => (a -> f b) -> s -> f t) -> p a b -> p s t
  {-default traversal :: (forall ff bb aa. c ff => c (O ff (Bazaar c bb aa))-}
                       {-,c I , c (Baz c t b))-}
                    {-=> (forall f. c f => (a -> f b) -> s -> f t)-}
                    {--> p a b -> p s t-}
  {-traversal f pab = promap (\s -> Baz (\afb -> f afb s)) (sold @c) (traversed @c pab)-}
  mapping :: c ~ Wrap => ((a -> b) -> s -> t) -> p a b -> p s t
  mapping abst = traversal \ afb -> abst (afb > unwrap) > pure
  mapped :: c ~ Wrap => Map f => p a b -> p (f a) (f b)
  mapped = mapping map

  lens :: c ~ Map => (s -> a) -> (s -> b -> t) -> p a b -> p s t
  lens get set = traversal \ afb s -> set s `map` afb (get s)
  _2 :: c ~ Map => p a b -> p (x,a) (x,b)
  _2 = traversed
  _1 :: c ~ Map => p a b -> p (a,x) (b,x)
  _1 p = let swap (a,b) = (b,a) in promap swap swap (_2 p)

  {-folding :: c ~ (Applicative & Comap)-}
          {-=> (forall m. Monoid m => (a -> m) -> s -> m)-}
          {--> p a b -> p s t-}
  {-folding amsm p = traversal (\afb -> amsm (\a ->  afb a)) p-}

{-app :: (Applicative f, Comap f) => f a -> f a -> f a-}
{-app (comap absurd -> fa) (comap absurd -> fb) = map absurd (fa . fb)-}

mapping_traversal :: Traversed Wrap p
                  => (forall f. Wrap f => (a -> f b) -> s -> f t)
                  -> p a b -> p s t
mapping_traversal afbsft = mapping \ ab -> unI < afbsft (I < ab)

lens_traversal :: Lensed p
               => (forall f. Map f => (a -> f b) -> s -> f t)
               -> p a b -> p s t
lens_traversal f = lens (f K > unK) (f \ _ -> id)

lens0 :: (Prismed p, Lensed p) => (s -> E t a) -> (s -> b -> t) -> p a b -> p s t
lens0 get set pab = promap (\s -> (get s, s)) (\(bt,s) -> case bt of {L t -> t; R b -> set s b}) (_1 (_R pab))

-- | 'Closed' over @(~) (E x))@
class Promap p => Prismed p where
  {-# minimal prism | _R #-}
  prism :: (s -> E t a) -> (b -> t) -> p a b -> p s t
  prism pat constr = promap pat (id ||| constr) < _R
  _R ::  p a b -> p (E x a) (E x b)
  _R = prism (L < L ||| R)  R
  _L :: p a b -> p (E a y) (E b y)
  _L = promap swap swap < _R

class Prismed p => From p where
  {-# minimal from | precoerce #-}
  from :: (b -> t) -> p a b -> p s t
  from bt p = precoerce (postmap bt p)
  precoerce :: p a x -> p s x
  precoerce = from \ x -> x

newtype instance (From ### p) a b = From (p a b) deriving newtype From
  deriving (Map,Remap,Map_) via (Promap ### From ### p) a
  deriving Promap_ via Promap ### From ### p
instance From p => Prismed (From ### p) where prism _ = from
instance From p => Promap  (From ### p) where promap _ = from

class ((forall x y a b . (a =# x,y =# b) => p x y =# p a b),Promap_ p) => Representational2 p
instance ((forall x y a b . (a =# x,y =# b) => p x y =# p a b), Promap_ p)=> Representational2 p

-- * Instances

instance Promap (->) where
  promap  = \f g p s -> g (p (f s))
  premap  = \f p s -> p (f s)
  postmap = \g p a -> g (p a)
instance Promap_ (->) where promap_ _ _ = coerce
instance Closed  (->)     where distributed = map; closed f = (f <)
{-instance Wrap ==> c => Traversed c (->) where-}
instance Traversed Wrap (->) where
 traversed = map
 traversal = mapping_traversal
 {-traversal l f s = case l (\a -> I (f a)) s of {I t -> t} -}
 lens sa sbt ab = \s -> sbt s (ab (sa s))
 mapping = id

{-instance Mapped (->) where-}
  {-mapping = id-}
  {-mapped = map-}
instance Prismed (->) where _R ab = \case {L x -> L x; R a -> R (ab a)}
instance Compose (->) where compose = (>)
instance Identity (->) where identity = id
instance Category (->)
instance Arr (->) where arr = id

deriving via (Representational ## Baz c t b) instance Map_ (Baz c t b)
deriving via (Map ## Baz c t b) instance Remap (Baz c t b)
instance Map (Baz c t b) where
  map xy (Baz xfbft) = Baz \ yfb -> xfbft \ x -> yfb (xy x)

{-instance (forall f x. c (O f (Bazaar c x b)), forall x. c (K x), c ==> Remap)-}
instance (forall f x. c (O f (Bazaar c x b)), forall x. c (K x), c ==> Remap)
  => Traverses c (Baz c t b) where
     traverses f (Baz bz) = map_ Baz_ (unO (bz (\x -> O (remap buy (sell @c) (f x)))))

instance (c ==> Map, c (Bazaar c a b)) => Map (Bazaar c a b) where
  map f (Bazaar m) = Bazaar (\afb -> map f (m afb))
  {-map f (Bazaar m) = Bazaar (map f < m)-}
instance c ==> Map_ => Map_ (Bazaar c a b)
  where map_ f (Bazaar m) = Bazaar (map_ f < m)
instance c ==> Remap => Remap (Bazaar c a b) where
  remap f g (Bazaar m) = Bazaar (\k -> remap f g (m k))
instance (c (Bazaar c a b), c ==> Pure) => Pure (Bazaar c a b) where
  pure t = Bazaar (pure t!)

instance (c (Bazaar c a b), c ==> Apply) => Apply (Bazaar c a b) where
  Bazaar afbfxy `ap` Bazaar afbfx = Bazaar \ afb -> afbfxy afb |$| afbfx afb
instance (c (Bazaar c a b), c ==> Applicative) => Applicative (Bazaar c a b)
instance (c (Bazaar c a b), c ==> Monad) => Monad (Bazaar c a b) where
  bind abz (Bazaar xmyma) = Bazaar \ xmy ->
    (`bind` xmyma xmy) \ a -> case abz a of Bazaar xmymb -> xmymb xmy

{-instance (c (Bazaar c a b), c ==> Monad) => Monad (Bazaar c a b) where-}
  {-traverses afb (Bazaar agyga) = -}

    


{-instance {-# Overlappable #-} Promap p => Promap_ p where-}
  {-promap_ _ _ !p = promap coerce coerce p-}
-- |A @Pure f@ distributes through Sum types:
--  http://r6research.livejournal.com/28338.html
{-instance {-# Overlappable #-} (Pure t, Zero x) => One (t x) where one = pure zero-}


type family Left t where Left (E a b) = a
type family Right t where Right (E a b) = b
class a ~ E (Left a) (Right a) => IsEither' a
instance a ~ E (Left a) (Right a) => IsEither' a


instance {-# overlappable #-} (Arr p, Lensed p) => Arrow p
instance {-# overlappable #-} (Arr p, Prismed p) => ArrowChoice p

type Category# = PC.Category
newtype instance (Category# ### p) a b = Category# (p a b)
  deriving newtype Category#
instance Category# p => Compose (Category# ### p) where compose q p = p PC.. q
instance Category# p => Identity (Category# ### p) where identity = PC.id
instance Category# p => Category (Category# ### p)

newtype instance (Category ### p) a b = Category (p a b)
  deriving newtype (Category,Compose,Identity,Promap,Promap_)
  deriving (Map,Remap,Map_) via (Category ### p) a
instance (Category p , Promap p) => Arr (Category ### p)

newtype instance (Arr ### p) a b = Arr (p a b)
  deriving newtype (Arr,Compose)
  deriving Promap_ via Promap ### Arr ### p
instance Arr p => Identity (Arr ### p) where identity = arr id
instance Arr p => Category (Arr ### p)
instance Arr p => Promap (Arr ### p) where promap f g p = arr f >>> p >>> arr g
deriving via (Promap ### Arr ### p) a instance Arr p => Map ((Arr ### p) a)
deriving via (Promap ### Arr ### p) a instance Arr p => Remap ((Arr ### p) a)
deriving via (Promap ### Arr ### p) a instance Arr p => Map_ ((Arr ### p) a)

newtype instance (Arrow ### p) a b = Arrow (p a b)
  deriving newtype Arrow
  deriving (Arr,Category,Compose,Identity,Promap,Promap_) via Arr ### p
  deriving (Map,Remap,Map_) via (Arr ### p) a

instance (Arrow p) => Traversed Map (Arrow ### p) where
  traversal = lens_traversal
  lens sa sbt pab = arr (\s -> (sbt s,sa s))  >>> (identity *** pab) >>> arr (\(f,a) -> f a)
  _1 = (*** identity)
  _2 = (identity ***)

type Arrow# p = P.Arrow

instance {-# overlappable #-} Category p => PC.Category p
  where p . q = compose q p; id = identity

instance {-# overlappable #-} Arrow p => P.Arrow p
  where arr = arr; (***) = (***); (&&&) = (&&&)
instance {-# overlappable #-} (Arrow p, ArrowChoice p) => P.ArrowChoice p where
  p +++ q = either2e >^ p +++ q ^> e2either
    where e2either = \case L a -> P.Left a; R b -> P.Right b
          either2e = \case P.Left a -> L a; P.Right b -> R b
  p ||| q = either2e >^ p ||| q
    where either2e = \case P.Left a -> L a; P.Right b -> R b

newtype instance (Promap ### p) a b = Promap (p a b)
  deriving newtype Promap
  deriving (Remap,Map_) via (Promap ### p) a
instance Promap p => Map ((Promap ### p) a) where map f (Promap p) = Promap (postmap f p)
instance Promap p => Promap_ (Promap ### p) where
{-instance {-# overlappable #-} Promap p => Promap_ p where-}
  promap_ _ _ !p = promap coerce coerce p
  premap_ _ !p = premap coerce p
  postmap_ _ !p = postmap coerce p

newtype instance (Promap_ ### p) a b = Promap_ (p a b) deriving newtype Promap_
instance Promap_ p => Map_ ((Promap_ ### p) a) where
  map_ f (Promap_ p) = Promap_ (postmap_ f p)

newtype instance (Representational2 ### p) a b = Representational2 (p a b)
  deriving Map_ via (Promap_ ### p) a
instance Representational2 p => Promap_ (Representational2 ### p)
  where promap_  _ _ = coerce

{-newtype Ar a b = Ar (a -> b)-}
  {-deriving newtype (Promap, Promap_, Map_)-}
  {-deriving (Map) via Promap ### Ar a-}

{-instance Bind I (Baz c t b) where bind = map_bind-}
{-deriving via (Promap ### (Baz c t) b) instance Promap (Baz c t) => Bind I (Baz c t b)-}

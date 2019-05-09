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
class (Arr p, Strong p) => Arrow p where
  (***) :: p x a -> p y b -> p (x,y) (a,b)
  p *** q = _1 p >>> _2 q
  (&&&) :: p x a -> p x b -> p x (a,b)
  p &&& q =  p *** q ^< \ a -> (a,a)
class (Arr p, Choice p) => ArrowChoice p  where
  (+++) :: p x a -> p y b -> p (E x y) (E a b)
  p +++ q = _L p >>> _R q
  (|||) :: p x a -> p y a -> p (E x y) a
  p ||| q =  p +++ q ^> (\case L a -> a; R a -> a)

infixl 2 |||, +++
infixl 3 &&&, ***


---- * Promap
class (forall x. Map_ (p x)) => Promap_ p where
  {-# minimal promapAs | premapAs ,postmapAs #-}
  promapAs :: (s =# a, b =# t) => p a b -> p s t
  promapAs = premapAs > postmapAs
  premapAs :: forall s a t. (s =# a) => p a t -> p s t
  premapAs = promapAs @p @s @a @t @t
  postmapAs :: forall b t s. (t =# b) => p s b -> p s t
  postmapAs = promapAs @p @s @s @b @t

promap_ :: (Promap_ p, s =# a, b =# t) => (s -> a) -> (b -> t) -> p a b -> p s t
promap_ _ _ = promapAs
premap_ :: (Promap_ p, s =# a) => (s -> a) -> p a t -> p s t
premap_ _ = premapAs
postmap_ :: (Promap_ p, b =# t) => (b -> t) -> p s b -> p s t
postmap_ _ = postmapAs

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

---- * Closed
class Promap p => Closed p where
  distributed :: forall t a b. Distribute t => p a b -> p (t a) (t b)
  distributed = zipping zipWithF
  closed :: p a b -> p (x -> a) (x -> b)
  closed = distributed
  grate :: (((s -> a) -> b) -> t) -> p a b -> p s t
  grate sa_b_t = \ab -> promap (\a g -> g a) sa_b_t (distributed ab)
  zipping :: (forall f. Map f => (f a -> b) -> f s -> t) -> p a b -> p s t
  zipping sabsst = grate (`sabsst` \ s -> s)

--[>(./) :: (Fold Add0 t, Add0 m) => t a -> (a -> m) -> m<]
--[>(./) = for_ @Add0<]
--[>(+/) :: (Fold Add0 t, Add0 m) => t a -> (a -> m) -> m<]
--[>(+/) = for_ @Add0<]
--[>(*/) :: (Fold Mul1 t, Mul1 m) => t a -> (a -> m) -> m<]
--[>(*/) = for_ @Mul1<]


cocollect :: forall f t a b. (Traverses Map t, Map f)
           => (t a -> b) -> t (f a) -> f b
cocollect tab tfa = map tab (sequenceC @Map tfa)

class Promap p => Strong p where
  lensed :: Traverses Map t => p a b -> p (t a) (t b)
  lensed = lensing (traverses @Map)
  lensing :: (forall f. Map f => (a -> f b) -> s -> f t) -> p a b -> p s t
  lensing f = lens (f K > unK) (f \ _ -> id)
  lens :: (s -> a) -> (s -> b -> t) -> p a b -> p s t
  lens get set = lensing \ afb s -> set s `map` afb (get s)
  _2 :: p a b -> p (x,a) (x,b)
  _2 = lensed
  _1 :: p a b -> p (a,x) (b,x)
  _1 p = let swap (a,b) = (b,a) in promap swap swap (_2 p)

newtype instance (Strong ### p) a b = Strong (p a b)
  deriving newtype Strong
  deriving Promap_ via Promap ### Strong ### p
  deriving (Map,Map_,Remap) via (Promap ### Strong ### p) a
instance Strong p => Promap (Strong ### p) where promap f g = lens f (g!)

  --[>folding :: c ~ (Applicative & Comap)<]
          --[>=> (forall m. Monoid m => (a -> m) -> s -> m)<]
          --[>-> p a b -> p s t<]
  --[>folding amsm p = traversal (\afb -> amsm (\a ->  afb a)) p<]

--[>app :: (Applicative f, Comap f) => f a -> f a -> f a<]
--[>app (comap absurd -> fa) (comap absurd -> fb) = map absurd (fa . fb)<]

class Strong p => Traversed1 p where
--  {-# minimal traversal1 | traversed1 #-}
  traversed1 :: Traverses Apply t => p a b -> p (t a) (t b)
  traversed1 = traversal1 (traverses @Apply)
  traversal1 :: (forall f. Apply f => (a -> f b) -> s -> f t) -> p a b -> p s t
  --traversal1 f pab = promap (\s -> Baz \ afb -> f afb s) (sold @Apply) (traversed1 pab)

newtype instance (Traversed1 ### p) a b = Traversed1 (p a b)
  deriving newtype Traversed1
  deriving (Promap,Promap_) via Strong ### Traversed1 ### p
  deriving (Map,Map_,Remap) via (Strong ### Traversed1 ### p) a
instance Traversed1 p => Strong (Traversed1 ### p) where
  lensed = traversed1
  lensing = traversal1

class (Strong p, Choice p) => Traversed0 p where
  traversal0 :: (forall f. Pure f => (a -> f b) -> s -> f t) -> p a b -> p s t
  traversal0 afbsft = lens0 (\s -> swap (afbsft L s)) (\ s b -> case afbsft (\_ -> I b) s of I t -> t)
  traversed0 :: Traverses Pure t => p a b -> p (t a) (t b)
  traversed0 = traversal0 (traverses @Pure)
  lens0 :: (s -> E t a) -> (s -> b -> t) -> p a b -> p s t
  lens0 get set pab = promap (\s -> (get s, s)) (\(bt,s) -> case bt of {L t -> t; R b -> set s b}) (_1 (_R pab))

newtype instance (Traversed0 ### p) a b = Traversed0 (p a b)
  deriving newtype Traversed0
  deriving (Promap,Promap_) via Strong ### Traversed0 ### p
  deriving (Map,Map_,Remap) via (Strong ### Traversed0 ### p) a
instance Traversed0 p => Strong (Traversed0 ### p) where _2 = traversed0
instance Traversed0 p => Choice (Traversed0 ### p) where _R = traversed0

class (Traversed0 p, Traversed1 p) => Traversed p where
--  {-# minimal traversal | traversed #-}
  traversed :: Traverses Applicative t => p a b -> p (t a) (t b)
  traversed = traversal (traverses @Applicative)
  traversal :: (forall f. Applicative f => (a -> f b) -> s -> f t) -> p a b -> p s t
  --traversal f pab = promap (\s -> Baz \ afb -> f afb s) (sold @Applicative) (traversed pab)

newtype instance (Traversed ### p) a b = Traversed (p a b)
  deriving newtype Traversed
  deriving (Strong, Choice, Promap, Promap_) via Traversed0 ### Traversed ### p
  deriving (Map, Map_,Remap) via (Traversed1 ### Traversed ### p) a
instance Traversed p => Traversed0 (Traversed ### p) where
  traversed0 = traversed
  traversal0 = traversal
instance Traversed p => Traversed1 (Traversed ### p) where
  traversed1 = traversed
  traversal1 = traversal

class (Closed p, Traversed p) => Mapped p where
  {-# minimal mapping | setter #-}
  mapping :: (forall f. Wrap f => (a -> f b) -> s -> f t) -> p a b -> p s t
  -- TODO: make default depend on mapped
  mapping afbsft = setter \ ab s -> case afbsft (\a -> I (ab a)) s of I t -> t
  setter :: ((a -> b) -> s -> t) -> p a b -> p s t
  setter abst = mapping \ afb -> abst (afb > unwrap) > pure
  mapped :: Map f => p a b -> p (f a) (f b)
  mapped = setter map

newtype instance (Mapped ### p) a b = Mapped (p a b)
  deriving newtype Mapped
  deriving Promap_ via Promap ### p
  deriving (Map,Map_,Remap) via (Promap ### p) a
instance Mapped p => Promap (Mapped ### p) where promap = setter << promap
instance Mapped p => Traversed1 (Mapped ### p) where
  traversal1 = mapping
  traversed1 = mapped
instance Mapped p => Traversed0 (Mapped ### p) where
  traversal0 = mapping
  traversed0  = mapped
instance Mapped p => Choice (Mapped ### p) where
  prism seta bt = setter \ ab -> seta > (id  ||| ab > bt)
  _R = mapped
  _L = promap swap swap < mapped
instance Mapped p => Traversed (Mapped ### p) where
  traversal = mapping
  traversed = mapped
instance Mapped p => Strong (Mapped ### p) where
  lensed = mapped
  lensing = mapping
  lens sa sbt = setter \ ab s -> s % sa > ab > sbt s
instance Mapped p => Closed (Mapped ### p) where 
  closed = mapped
  distributed = mapped
  --zipping fab fs = 


---- | 'Closed' over @(~) (E x))@
class Promap p => Choice p where
  {-# minimal prism | _R #-}
  prism :: (s -> E t a) -> (b -> t) -> p a b -> p s t
  prism pat constr = promap pat (id ||| constr) < _R
  _R ::  p a b -> p (E x a) (E x b)
  _R = prism (L < L ||| R)  R
  _L :: p a b -> p (E a y) (E b y)
  _L = promap swap swap < _R
  --prismed :: (Pure t, Traverses Pure t) => p a b -> p (t a) (t b)
  --prismed = prism (swap < traverses @Pure L) pure

newtype instance (Choice ### p) a b = Choice (p a b)
  deriving newtype Choice
  deriving Promap_ via Promap ### Choice ### p
  deriving (Map,Map_,Remap) via (Promap ### Choice ### p) a
instance Choice p => Promap (Choice ### p) where
  promap sa bt = prism (sa > R) bt

--Pure f => f a -> E (f b) a

class Choice p => From p where
  {-# minimal from | precoerce #-}
  from :: (b -> t) -> p a b -> p s t
  from bt p = precoerce (postmap bt p)
  precoerce :: p a x -> p s x
  precoerce = from \ x -> x

newtype instance (From ### p) a b = From (p a b) deriving newtype From
  deriving (Map,Remap,Map_) via (Promap ### From ### p) a
  deriving Promap_ via Promap ### From ### p
instance From p => Choice (From ### p) where prism _ = from
instance From p => Promap  (From ### p) where promap _ = from

class ((forall x y a b . (a =# x,y =# b) => p x y =# p a b),Promap_ p) => Representational2 p
instance ((forall x y a b . (a =# x,y =# b) => p x y =# p a b), Promap_ p)=> Representational2 p

---- * Instances

instance Promap (->) where
  promap  = \f g p s -> g (p (f s))
  premap  = \f p s -> p (f s)
  postmap = \g p a -> g (p a)
instance Promap_ (->) where promapAs = coerce
instance Closed  (->)     where distributed = map; closed f = (f <)

deriving via (Mapped ### (->)) instance Traversed (->)
deriving via (Mapped ### (->)) instance Traversed0 (->)
deriving via (Mapped ### (->)) instance Traversed1 (->)
 --traversal l f s = case l (\a -> I (f a)) s of {I t -> t} 
instance Strong (->) where lens sa sbt ab = \s -> sbt s (ab (sa s))
instance Mapped (->) where
  setter = id
  mapped = map
instance Choice (->) where _R ab = \case {L x -> L x; R a -> R (ab a)}
instance Compose (->) where compose = (>)
instance Identity (->) where identity = id
instance Category (->)
instance Arr (->) where arr = id

{-
 -instance {-# Overlappable #-} Promap p => Promap_ p where
 -  promapAs !p = promap coerce coerce p
 -}

---- |A @Pure f@ distributes through Sum types:
----  http://r6research.livejournal.com/28338.html
--[>instance {-# Overlappable #-} (Pure t, Zero x) => One (t x) where one = pure zero<]


--type family Left t where Left (E a b) = a
--type family Right t where Right (E a b) = b
--class a ~ E (Left a) (Right a) => IsEither' a
--instance a ~ E (Left a) (Right a) => IsEither' a


instance {-# overlappable #-} (Arr p, Strong p) => Arrow p
instance {-# overlappable #-} (Arr p, Choice p) => ArrowChoice p

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

-- ----------------------------------------
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

instance (Arrow p) => Strong (Arrow ### p) where
  lens sa sbt pab = arr (\s -> (sbt s,sa s))  >>> (identity *** pab) >>> arr (\(f,a) -> f a)
  _1 = (*** identity)
  _2 = (identity ***)

--type Arrow# p = P.Arrow

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
--[>instance {-# overlappable #-} Promap p => Promap_ p where<]
  promapAs !p = promap coerce coerce p
  premapAs !p = premap coerce p
  postmapAs !p = postmap coerce p

newtype instance (Promap_ ### p) a b = Promap_ (p a b) deriving newtype Promap_
instance Promap_ p => Map_ ((Promap_ ### p) a) where
  mapAs (Promap_ p) = Promap_ (postmapAs p)

newtype instance (Representational2 ### p) a b = Representational2 (p a b)
  deriving Map_ via (Promap_ ### p) a
instance Representational2 p => Promap_ (Representational2 ### p) where promapAs = coerce

{-# language TemplateHaskell,QuasiQuotes #-}
{-# language UndecidableInstances #-}
{-# language MagicHash #-}
module Optic where
import Types
import Fun
import Control
import Type.E
import Type.K
import Type.I
import qualified Prelude as P
import qualified Data.Set as P
import Functor
import Data

-- * SETTER

set :: ((a -> b) -> s -> t) -> b -> s -> t
set l b s = l (\_ -> b) s

{-update l f s = l f s-}

-- * GRATE

newtype Grate a b s t = Grate {runGrate :: (((s -> a) -> b) -> t)}
  deriving (Map_,Remap,Map) via (Promap ### Grate a b) s
  deriving (Promap_)                       via (Promap ### Grate a b)
instance Promap (Grate a b) where
  promap sa bt (Grate aabb) = Grate \ sab -> bt $ aabb \ aa -> sab \ s -> aa (sa s)
instance Closed (Grate a b) where
  closed (Grate z) = Grate \ f x -> z \ k -> f \ g -> k (g x)

withGrate :: (Grate a b a b -> Grate a b s t) -> ((s -> a) -> b) -> t
withGrate g = case g (Grate (\f -> f (\x -> x))) of Grate z -> z

cloneGrate :: forall p a b s t. Closed p => (Grate a b a b -> Grate a b s t) -> p a b -> p s t
cloneGrate g = grate (withGrate g)

zipOf' :: Map f => Grate a b s t -> (f a -> b) -> f s -> t
zipOf' (Grate g) reduce fs = g (\get -> reduce (map get fs))

grate0 :: Grate a b a b
grate0 = Grate ($ id)

repGrate :: (Grate a b a b -> Grate a b s t) -> Grate a b s t
repGrate = ($ grate0)

zipOf :: Map f => (Grate a b a b -> Grate a b s t) -> (f a -> b) -> f s -> t
zipOf g reduce fs = g grate0 `runGrate` \get -> reduce (map get fs)

-- * ZIP2

newtype Zip2 a b = Zip2 {runZip2 :: a -> a -> b}
  deriving (Map_,Remap,Map) via (Promap ### Zip2) a
  deriving (Monoidal (,)) via Apply ## Zip2 a -- TODO: roll into profunctor apply
  deriving Promap_ via Representational2 ### Zip2
  deriving anyclass Applicative
instance Promap Zip2 where promap f g (Zip2 z) = Zip2 \ a a' -> g (z (f a) (f a'))
instance Closed Zip2 where closed (Zip2 z) = Zip2 \ xa xa' x -> z (xa x) (xa' x)
instance Apply (Zip2 x) where Zip2 xxab `ap` Zip2 xxa = Zip2 \ x x' -> xxab x x' (xxa x x')
instance Pure (Zip2 x) where pure a = Zip2 \ _ _ -> a

_Zip2_ :: forall p a b s t. Promap_ p => Zip2 a b `p` Zip2 s t -> (a -> a -> b) `p` (s -> s -> t)
_Zip2_ = promap_ Zip2 runZip2

-- * ISO

data Iso a b s t = Iso (s -> a) (b -> t)
  deriving (Map_,Remap,Map) via (Promap ### (Iso a b)) s
  deriving Promap_ via Promap ### Iso a b
instance Promap (Iso a b) where promap f g (Iso sa bt) = Iso (f > sa) (g < bt)

runIso (Iso sa bt) ab = sa > ab > bt

repIso :: (forall p. Promap p => p a b -> p s t) -> Iso a b s t
repIso p = p (Iso (\a -> a) (\b -> b))

_coerce_ :: forall s t a b p. (Promap_ p, s =# a, b =# t ) => p a b -> p s t
_coerce_ = promapAs


-- * Traversing

newtype Traversing f a (b :: *) = Traversing {runTraversing :: a -> f b}
  deriving (Map) via (Promap ### Traversing f) a
-- | Lift an f-operation over the target of a traversal
_Traversing_ :: (Traversing f a b -> Traversing f s t) -> (a -> f b) -> s -> f t
_Traversing_ = promap_ Traversing runTraversing

forOf :: (Traversing f a b -> Traversing f s t) -> s -> (a -> f b) -> f t
forOf l s = _Traversing_ l .$ s


-- | ex:
--
-- > [1,2,3] & traversed @@~ print
(@@~) :: (Traversing f a b -> Traversing f s t) -> (a -> f b) -> s -> f t
(@@~) = _Traversing_
infixl 2 @@~ --TODO: fix

instance Map f => Promap (Traversing f)
  where promap f g (Traversing s) = Traversing (promap f (map g) s)
instance Remap f => Remap (Traversing f a)
  where remap f g (Traversing s) = Traversing (remap f g < s)
instance Map_ f => Map_ (Traversing f a)
  where mapAs (Traversing s) = Traversing (mapAs < s)
instance Map_ f => Promap_ (Traversing f) where
  premapAs = coerce
  postmapAs (Traversing afb) = Traversing $ afb > map_ coerce
instance  Distribute f => Closed (Traversing f) where
  distributed (Traversing afb) = Traversing (collect afb)
instance Map f => Traversed Map (Traversing f) where
  traversal afbsft (Traversing afb) = Traversing (afbsft afb)

-- * PRISM

_Just :: Prismed p => p a b -> p (Maybe a) (Maybe b)
_Just = prism .$ Just $ \case {Nothing -> L Nothing; Just a -> R a}

_Nothing :: Prismed p => p () () -> p (Maybe a) (Maybe a)
_Nothing = prism .$ (Nothing!) $ \case {Nothing -> R (); Just a -> L (Just a)}

data Prism a b s t = Prism (s -> E t a) (b -> t)
  deriving (Map,Remap) via (Promap ### Prism a b) s
  deriving Promap_ via Representational2 ### Prism a b
  deriving Map_ via (Representational2 ### Prism a b) s
_Prism_ :: (Prism a b a b -> Prism a b s t) -> ((s -> E t a) -> (b -> t) -> r) -> r
_Prism_ l k = case l (Prism R \ x -> x) of Prism h g -> k h g

-- TODO: op gelisam's case matcher
match :: (Prism a b a b -> Prism a b s t) -> (t -> r) -> (a -> r) -> s -> r
match l kt ka = _Prism_ l (\pat _ -> \s -> case pat s of {L t -> kt t; R a -> ka a})

-- | Use a @Prism@ in a simple case-like match, providing a default result for if it doesn't match,     and a continuation for what to do if it does.
match' :: (Prism a b a b -> Prism a b s t) -> r -> (a -> r) -> s -> r
match' l r ka = _Prism_ l (\pat _ -> \s -> case pat s of {L _ -> r; R a -> ka a})


-- | Try to view the target of a @Prism@
preview :: (Prism a b a b -> Prism a b s t) -> s -> Maybe a
preview l = match' l Nothing Just


instance Promap (Prism a b) where
  promap f g (Prism seta bt) = Prism (((L < g) ||| R) < seta < f) (g < bt)
instance Prismed (Prism a b) where
  prism seta bt (Prism aeba bb) = Prism (seta > (L ||| (aeba > (bt +++ id)))) (bb > bt)
  {-_R (Prism seta bt) = Prism (L +++ (seta > (R ||| R(R < bt)-}
  _R (Prism seta bt) = (`Prism` (R < bt)) \case 
    L t -> L $ L t
    R s -> case seta s of {L t -> L (R t); R a -> R a}

newtype View r a (b :: *) = View {runView :: a -> r}
  deriving (Map, Remap) via (Promap ### View r) a
  deriving Map_ via Representational ## View r a
  deriving Promap_ via Representational2 ### View r
_View_ :: Promap_ p => p (View n a b) (View m s t) -> p (a -> n) (s -> m)
_View_ = promap_ View runView

instance Promap (View r) where promap f g (View an) = View \ s -> an (f s)
instance Traversed (Map & Comap) (View m) where
  traversal akmskm (View am) = View (unK < akmskm (K < am))

newtype Review (a :: *) b = Review {runReview :: b}
  deriving (Prismed,Promap) via From ### Review
  deriving (Map,Remap) via (Promap ### Review) a
  deriving Promap_ via Representational2 ### Review
  deriving Map_ via Representational ## (Review a)
instance From Review where from bt (Review b) = Review (bt b)


newtype Do f (r :: *) a (b :: *) = Do {runDo :: a -> f r}
  deriving (Map,Remap,Map_) via Phantom ## Do f r a
  deriving Promap_ via Representational2 ### Do f r
_Do_ :: Promap_ p => p (Do f r a b) (Do g r' s t) -> p (a -> f r) (s -> g r')
_Do_ = promap_ Do runDo

instance Promap (Do f r) where promap f _ (Do b) = Do (f > b)

-- | Ex: @doWith _1 print :: (Zero r, Show a) => (a,x) -> IO r
doWith :: (Do (FK f x) x a b -> Do (FK f x) x s t) -> (a -> f x) -> s -> f x
doWith l afx = case l < Do $ FK < afx of Do sfkx -> sfkx > \case FK fx -> fx

doFor :: Map f => (Do (FK f x) x a b -> Do (FK f x) x s t) -> s -> (a -> f x) -> f x
doFor l s = doWith l .$ s

instance Traversed (Map & Comap) (Do f r) where
  traversal afbsft (Do afr) = Do (unK < (afbsft (K < afr)))

newtype FK f a b = FK {runFK :: f a}
  deriving (Map,Remap,Map_) via Phantom ## FK f a

{-instance Apply f => Monoidal (,) (FK f a) where monoidal (FK fa) (FK fb) = FK (liftA2 (\_ b -> b) fa fb)-}
{-instance Apply f => Apply (FK f a) where ap (FK fa) (FK fb) = FK (liftA2 (\_ b -> b) fa fb)-}
{-instance (Pure f, Nil a) => Pure (FK f a) where pure !_ = FK (pure nil)-}
{-instance (Applicative f, Nil a) => Applicative (FK f a)-}
instance (Pure f, Nil a) => Nil (FK f a r) where nil = FK (pure nil)
instance (Apply f, Op a) => Op (FK f a r) where FK f `op` FK g = FK (f |$ op $| g)
instance (Applicative f, Scale0 a) => Scale0 (FK f a r)


{-newtype WrapF f a = WrapF {unwrapF :: f a}-}
{-instance (Pure f, Zero a) => Zero (WrapF f a) where zero = WrapF (pure zero)-}
{-instance (Apply f, Op a) => Op (WrapF f a) where op (WrapF a) (WrapF b) = WrapF (op `map` a `ap`     b)-}
{-instance (Applicative f, Scale0 a) => Scale0 (WrapF f a)-}

newtype Update b s t = Update {runUpdate :: b -> s -> t}
  deriving (Map,Remap) via (Promap ### Update b) s
  deriving Promap_ via Representational2 ### Update b
  deriving Map_ via Representational ## Update b s
instance Promap (Update b) where promap f g (Update bst) = Update \ b -> f > bst b > g
instance Closed (Update b) where closed (Update bst) = Update \ b xs x -> bst b (xs x)
instance Prismed (Update b) where
  prism seta bt (Update bab) = Update \ b -> seta > (id ||| (bab b > bt))
instance Traversed Wrap (Update b) where
  traversal afbsft (Update bab) = Update \ b -> unI < afbsft (I < bab b)

_Update_ :: Promap_ p => Update x a b `p` Update x s t -> (x -> a -> b) `p` (x -> s -> t)
_Update_ = promap_ Update runUpdate

{-# language TemplateHaskell,QuasiQuotes #-}
{-# language UndecidableInstances #-}
{-# language MagicHash #-}
module Optic where
import Types
import TV
import Impl hiding ((!))
import Fun
import Control
import Type.E
import Type.K
import Type.I
import qualified Prelude as P
import Functor
import Data

-- * SETTER

set :: ((a -> b) -> s -> t) -> b -> s -> t
set l b s = l (\_ -> b) s

-- * GRATE

newtype Grate a b s t = Grate {runGrate :: (((s -> a) -> b) -> t)}
  deriving (MapRep,Remap,Map) via (Promap ### Grate a b) s
  deriving (PromapRep)                       via (Promap ### Grate a b)
instance Promap (Grate a b) where
  promap sa bt (Grate aabb) = Grate \ sab -> bt $ aabb \ aa -> sab \ s -> aa (sa s)
instance Closed (Grate a b) where
  closed (Grate z) = Grate \ f x -> z \ k -> f \ g -> k (g x)

withGrate :: (Grate a b a b -> Grate a b s t) -> ((s -> a) -> b) -> t
withGrate g = case g (Grate (\f -> f (\x -> x))) of Grate z -> z

cloneGrate :: forall c p a b s t. Closed p => (Grate a b a b -> Grate a b s t) -> p a b -> p s t
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
  deriving (MapRep,Remap,Map) via (Promap ### Zip2) a
  deriving (Monoidal (,)) via Apply ## Zip2 a
  deriving PromapRep via Representational2 ### Zip2
  deriving anyclass Applicative
instance Promap Zip2 where promap f g (Zip2 z) = Zip2 \ a a' -> g (z (f a) (f a'))
instance Closed Zip2 where closed (Zip2 z) = Zip2 \ xa xa' x -> z (xa x) (xa' x)
instance Apply (Zip2 x) where Zip2 xxab |$| Zip2 xxa = Zip2 \ x x' -> xxab x x' (xxa x x')
instance Pure (Zip2 x) where pure a = Zip2 \ _ _ -> a

_Zip2_ :: forall p a b s t. PromapRep p => Zip2 a b `p` Zip2 s t -> (a -> a -> b) `p` (s -> s -> t)
_Zip2_ = promapRep Zip2 runZip2

-- * ISO

data Iso a b s t = Iso (s -> a) (b -> t)
  deriving (MapRep,Remap,Map) via (Promap ### (Iso a b)) s
  deriving PromapRep via Promap ### Iso a b
instance Promap (Iso a b) where promap f g (Iso sa bt) = Iso (f > sa) (g < bt)

repIso :: (forall p. Promap p => p a b -> p s t) -> Iso a b s t
repIso p = p (Iso (\a -> a) (\b -> b))

_coerce_ :: forall s t a b p. (PromapRep p, s =# a, b =# t ) => p a b -> p s t
_coerce_ = promapRep coerce coerce


-- * Traversing

newtype Traversing f a (b :: *) = Traversing {runTraversing :: a -> f b}
  deriving (Map) via (Promap ### Traversing f) a
-- | Lift an f-operation over the target of a traversal
_Traversing_ :: (Traversing f a b -> Traversing f s t) -> (a -> f b) -> s -> f t
_Traversing_ = promapRep Traversing runTraversing

(@@~) :: (Traversing f a b -> Traversing f s t) -> (a -> f b) -> s -> f t
(@@~) = _Traversing_

instance Map f => Promap (Traversing f)
  where promap f g (Traversing s) = Traversing (promap f (map     g) s)
instance Remap f => Remap (Traversing f a)
  where remap f g (Traversing s) = Traversing (remap f g < s)
instance MapRep f => MapRep (Traversing f a)
  where mapRep f (Traversing s) = Traversing (mapRep f < s)
instance MapRep f => PromapRep (Traversing f) where
  premapRep _ = coerce
  postmapRep _ (Traversing afb) = Traversing $ afb > mapRep coerce
instance  Distribute f => Closed (Traversing f) where
  distributed (Traversing afb) = Traversing (collect afb)
instance (Map ==> c, Map f) => TraversedC c (Traversing f) where
  traversalC afbsft (Traversing afb) = Traversing (afbsft afb)

-- * PRISM

_Just :: Prismed p => p a b -> p (Maybe a) (Maybe b)
_Just = prism (\case {Nothing -> L Nothing; Just a -> R a}) Just

data Prism a b s t = Prism (s -> E t a) (b -> t)
  deriving (Map,Remap) via (Promap ### Prism a b) s
  deriving PromapRep via Representational2 ### Prism a b
  deriving MapRep via (Representational2 ### Prism a b) s
_Prism_ :: (Prism a b a b -> Prism a b s t) -> ((s -> E t a) -> (b -> t) -> r) -> r
_Prism_ l k = case l (Prism R \ x -> x) of Prism h g -> k h g

match :: (Prism a b a b -> Prism a b s t) -> (t -> r) -> (a -> r) -> s -> r
match l kt ka = _Prism_ l (\pat _ -> \s -> case pat s of {L t -> kt t; R a -> ka a})

-- | Use a @Prism@ in a simple case-like match, providing a default result for if it doesn't match,     and a continuation for what to do if it does.
match' :: (Prism a b a b -> Prism a b s t) -> r -> (a -> r) -> s -> r
match' l r ka = _Prism_ l (\pat _ -> \s -> case pat s of {L _ -> r; R a -> ka a})


{--- | Try to view the target of a @Prism@-}
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

{-newtype View r a (b :: *) = View {runView :: a -> r}-}
{-_View_ :: PromapRep p => p (View n a b) (View m s t) -> p (a -> n) (s -> m)-}
{-_View_ = promapRep View runView-}

{-{-impl @Promap [t|View [tv|r|] |] Impl.$$ #promap [|\f g (View an) -> View \ s -> an (f s)|]-}-}
{-instance MapRep (View r x) where mapRep _ = coerce-}
{-instance Map (View r x) where map _ = coerce-}
{-instance Remap (View r x) where remap _ _ = coerce-}
{-instance Traverse IsI (View r x) where traverse _ = coerce-}
{-instance Strong (View r x) where strong _ = coerce-}
{-instance MapM I (View r x) where mapM _ = coerce-}
{-instance PromapRep (View r) where promapRep _ _ = coerce-}
{-instance Promap (View r) where promap f g (View an) = View \ s -> an (f s)-}
{-instance c m => Traversed (IsK c) (View m) where-}
  {-traversal akmskm (View am) = View (unK < akmskm (K < am))-}

{-{-instance Traverse (IsK P.Monoid) P.Set-}-}


{-# language ImpredicativeTypes #-}
{-# language EmptyCase #-}
{-# language UndecidableSuperClasses #-}
{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language InstanceSigs #-}
{-# language UndecidableInstances #-}
module Traverse where
import GHC.Types
import Impl
import TV
import qualified Prelude as P
import Bazaar
import E
import I
import O
import Unsafe.Coerce
import Data.Proxy
import Types
import K
import Fun hiding  ((!))
import IsEither
import Add
import Def
import Mul
import qualified Data.Coerce as GHC
import X

import Coerce

-- * Strong
class Remap f => Strong f where
  {-# minimal strong | strengthen #-}
  strong :: a -> f b -> f (a,b)
  strong = strengthen (\(a,_) -> a) (\(_,b) -> b) (,)
  strengthen :: (c -> a) -> (c -> b) -> (a -> b -> c) -> a -> f b -> f c
  strengthen f g h a fb = remap (\c -> (f c, g c)) (\(x,y) -> h x y) (strong a fb)
  fill :: a -> f () -> f a
  fill = strengthen (\a -> a) (\_ -> ()) (\a _ -> a)

-- * Coercemap
class Coercemap f where
  coercemap :: a =# b => (a -> b) -> f a -> f b
  default coercemap :: (Representational f, a =# b) => (a -> b) -> f a -> f b
  coercemap _ = coerce
  {-# INLINE coercemap #-}

-- * Promap
class (forall x. Map (f x)) => Postmap f
  where postmap :: (b -> t) -> f x b -> f x t
class Premap f where premap :: (s -> a) -> f a x -> f s x
class Coercepromap p where
  coercepromap :: (s =# a, b =# t) => (s -> a) -> (b -> t) -> p a b -> p s t
  default coercepromap :: (Representational1 p, s =# a, b =# t)
                       => (s -> a) -> (b -> t) -> p a b -> p s t
  coercepromap _ _ = coerce
class (Premap p, Postmap p, Coercepromap p) => Promap p
  where promap :: (s -> a) -> (b -> t) -> p a b -> p s t

-- * Closed
class Promap p => Closed p where
  distributed :: forall t a b. Distribute Map t => p a b -> p (t a) (t b)
  distributed = zipping (zipWithF @Map)
  closed :: p a b -> p (x -> a) (x -> b)
  closed = distributed
  grate :: (((s -> a) -> b) -> t) -> p a b -> p s t
  grate sa_b_t = \ab -> promap (\a g -> g a) sa_b_t (distributed ab)
  zipping :: (forall f. Map f => (f a -> b) -> f s -> t) -> p a b -> p s t
  zipping sabsst = grate (`sabsst` \ s -> s)

-- * Apply
class Map f => Apply f where ap :: f (a -> b) -> f a -> f b

-- * Applicative
class (Pure f, Apply f) => Applicative f
class Applicative f => Monad f where bind :: (a -> f b) -> f a -> f b
-- * Distribute
class (c ==> Map, Map t) => Distribute c t where
  distribute :: c f => f (t a) -> t (f a)
  distribute = collect @c \ x -> x
  zipWithF   :: c f => (f a -> b) -> f (t a) -> t b
  zipWithF fab = \fta -> map fab (distribute @c fta)
  collect :: c f => (a -> t b) -> f a -> t (f b)
  collect f a = zipWithF @c (\x -> x) (map f a)

distribute_pure :: Distribute IsEither t => a -> t a
distribute_pure a = (id ||| absurd) `map` distribute @IsEither (L a)
-- * Pure
-- | A @Pure f@ is a pointed functor with a particular inhabited shape singled out
class (Lifting Zero One f, Remap f) => Pure f where
  fone :: f ()
  fone = pure ()
  pure :: a -> f a
  pure a = remap (\_ -> ()) (\_ -> a) fone

pure_distribute :: (Map t, Pure t) => E x (t a) -> t (E x a)
pure_distribute = (pure < L) ||| map R

-- * Traverse
class Map t => Traverse c t where
  traverse :: c f => (a -> f b) -> t a -> f (t b)
  traverse afb ta = sequence @c (map afb ta)
  sequence :: c f => t (f a) -> f (t a)
  sequence = traverse @c \ x -> x

--- 
class (Traverse ((~) I) f, Strong f) => Map f where
  map :: (a -> b) -> f a -> f b
  constMap :: b -> f a -> f b
  constMap b = map \ _ -> b

map_traverse :: (I ~ f, Map t) => (a -> f b) -> t a -> f (t b)
map_traverse aib = I< map (unI< aib)

cocollect :: forall c f t a b. (Traverse c t, c ==> Map, c f)
          => (t a -> b) -> t (f a) -> f b
cocollect tab tfa = map tab (sequence @c tfa)

type Mapped = Traversed ((~) I)

class (Promap p, c ==> Map) => Traversed (c :: (* -> *) -> Constraint) p where
  traversed :: Traverse c t => p a b -> p (t a) (t b)
  traversed = traversal @c (traverse @c)
  traversal :: (forall f. c f => (a -> f b) -> s -> f t) -> p a b -> p s t
  default traversal :: (forall ff bb aa. c ff => c (O ff (Bazaar c bb aa))
                       ,c I , c (Baz c t b))
                    => (forall f. c f => (a -> f b) -> s -> f t)
                    -> p a b -> p s t
  traversal f pab = promap (\s -> Baz (\afb -> f afb s)) (sold @c) (traversed @c pab)

class Traversed Map p => Lensed p where
  lens :: (s -> a) -> (s -> b -> t) -> p a b -> p s t
  lens get set = traversal @Map \ afb s -> set s `map` afb (get s)
  _2 :: p a b -> p (x,a) (x,b)
  _2 = traversed @Map
  _1 :: p a b -> p (a,x) (b,x)
  _1 p = let swap (a,b) = (b,a) in promap swap swap (_2 p)

lens0 :: (Prismed p, Lensed p) => (s -> E t a) -> (s -> b -> t) -> p a b -> p s t
lens0 get set pab = promap (\s -> (get s, s)) (\(bt,s) -> case bt of {L t -> t; R b -> set s b}) (_1 (_R pab))

class Promap p => Prismed p where
  {-# minimal prism #-}
  prism :: (s -> E t a) -> (b -> t) -> p a b -> p s t
  prism pat constr = promap pat (id ||| constr) < _R
  _R ::  p a b -> p (E x a) (E x b)
  _R = prism (\case L t -> L (L t); R a -> R a) R
  _L :: p a b -> p (E a y) (E b y)
  _L = promap E.swap E.swap < _R

class Traversed IsEither p => Precoerce p where
  {-# minimal from | precoerce #-}
  from :: (b -> t) -> p a b -> p s t
  from bt p = precoerce (postmap bt p)
  precoerce :: p a x -> p s x
  precoerce = from \ x -> x




-- * Coerce
-- | Representational equality
type (=#) = Coercible
coerce :: b =# a => a -> b
coerce = GHC.coerce; {-# INLINE coerce #-}

-- | Representational Equality on functors
class    (forall a. f a =# g a) => Coercible1 f g
instance (forall a. f a =# g a) => Coercible1 f g
type (#=#) = Coercible1
coerce1 :: forall g f a. f #=# g => f a -> g a
coerce1 = GHC.coerce

-- | 'Representational' types. 
class    ((forall a b. a =# b => f a =# f b),Coercemap f) => Representational f
instance ((forall a b. a =# b => f a =# f b),Coercemap f) => Representational f
representational :: forall b a f. (a =# b, Representational f) => f a -> f b
{-# INLINE representational #-}
representational = GHC.coerce

-- | 'Phantom' types can ignore their type parameter. Instances are automatically provided by GHC
class    ((forall x y. f x =# f y)) => Phantom f
instance ((forall x y. f x =# f y)) => Phantom f
phantom :: forall b a f. Phantom f => f a -> f b
phantom = GHC.coerce @(f a) @(f b); {-# INLINE phantom #-}

class ((forall x y a b . (a =# x,y =# b) => p x y =# p a b),Coercepromap p) => Representational1 p
instance ((forall x y a b . (a =# x,y =# b) => p x y =# p a b), Coercepromap p)=> Representational1 p

-- * Remap
class Coercemap f => Remap f where remap :: (b -> a) -> (a -> b) -> f a -> f b

-- * Instances

instance Remap [] where remap _ = P.map
instance Strong [] where strong a = P.map (a,)
instance Map [] where map = P.map
instance Pure [] where pure a = [a]
instance (c ==> Applicative) => Traverse c [] where
  traverse f = go where
    go = \case
      [] -> pure []
      a : as -> (:) `map` f a `ap` go as
instance Distribute IsEither [] where
  distribute = \case {L x -> [L x]; R ts -> map R ts}
  zipWithF fab = \case
    L x -> [fab (L x)]
    R ta -> map (\a -> fab (R a)) ta
  collect atb = \case
    L x -> [L x]
    R a -> map R (atb a)

instance Remap   ((->) x) where remap _ f g = \a ->  f (g a)
instance Strong  ((->) x) where strong x g  = \a -> (x,g a)
instance Map     ((->) x) where map f g     = \a ->  f (g a)
instance Traverse ((~) I) ((->) x)    where traverse = map_traverse
instance Postmap (->)     where postmap     = map
instance Premap  (->)     where premap      = \f p a -> p (f a)
instance Promap  (->)     where promap      = \f g p a -> g (p (f a))
instance (c ==> Map, Map ((->) x)) => Distribute c ((->) x)
  where distribute fxa = \x -> map (\xa -> xa x) fxa
instance Closed  (->)     where distributed = map; closed f = (f <)
instance (c ==> Map, c I) => Traversed c (->) where
 traversed = map
 traversal l f s = case l (\a -> I (f a)) s of {I t -> t} 



instance Remap  (E x) where remap _ f = \case {L x -> L x; R a -> R (f a)}
instance Strong (E x) where strong x  = \case {L x -> L x; R a -> R (x,a)}
instance Map    (E x) where map f     = \case {L x -> L x; R a -> R (f a)}
instance Pure (E x)   where pure = R
instance (forall f. c f => (Pure f, Map f)) => Traverse c (E x) where
  traverse afb = \case {L x -> pure (L x); R a -> map R (afb a)}
instance Distribute IsEither (E x) where
  distribute = \case {L y -> R (L y); R (L x) -> L x; R (R a) -> R (R a)}

instance Remap I  where remap _ f (I a) = I (f a)
instance Strong I where strong x (I a)  = I (x,a)
instance Map I    where map f (I a)     = I (f a)
instance Pure I where pure = I
instance Apply I where ap (I f) (I a) = I (f a)
instance Applicative I
instance Traverse ((~) I) I    where traverse = map_traverse
instance (c ==> Map, Map I) => Distribute c I
  where distribute (fia :: f (I a)) = I (coercemap unI fia)

instance Remap ((,) x)  where remap _ f (x,a) = (x, f a)
instance Strong ((,) x) where strong y (x,a)  = (x,(y,a))
instance Map ((,) x)    where map f (x,a)     = (x, f a)
instance (c ==> Map, Map ((,) x)) => Traverse c ((,) x)
  where traverse f (x,a) = map (x,) (f a)

instance Map (K a) where map _ = coerce
instance Traverse ((~) I) (K a) where traverse = map_traverse
instance Remap (K a) where remap _ _ = coerce
instance Strong (K a) where strong _ = coerce
instance Zero a => Pure (K a) where pure _ = K zero
instance (c ==> Map, Def a, Map (K a)) => Distribute c (K a)
  where distribute _ = K def

instance Remap P.IO where remap _ = P.fmap
instance Strong P.IO where strong a = P.fmap (a,)
instance Map P.IO where map = P.fmap
instance Traverse ((~) I) P.IO where traverse = map_traverse

instance (Map f, Map g) => Map (O f g)
  where map f (O fg) = O (map (map f) fg)
instance (Map f, Map g) => Traverse ((~) I) (O f g) where traverse = map_traverse
instance (Remap f, Remap g) => Remap (O f g)
  where remap f g (O fg) = O (remap (remap g f) (remap f g) fg)
instance (Map f, Strong g) => Strong (O f g)
  where strong a (O fg) = O (map (strong a) fg)

instance Map (Baz c t b) where
  map xy (Baz xfbft) = Baz \ yfb -> xfbft \ x -> yfb (xy x)
instance Traverse ((~) I) (Baz c t b) where traverse = map_traverse
instance Remap (Baz c t b)
  where remap _ = map
instance Strong (Baz c t b)
  where strong x (Baz afbft) = Baz (\xafb -> afbft (\a -> xafb (x,a)))
instance (c ==> Map
         ,Map (Baz c t b)
         ,forall f b a. c f => c (O f (Bazaar c b a)))
  => Traverse c (Baz c t b) where
     traverse f (Baz bz) = map Baz_ (unO (bz (\x -> O (map (sell @c) (f x)))))

instance (c (Bazaar c a b), forall f. c f => Map f) => Map (Bazaar c a b) where
  map f (Bazaar m) = Bazaar (\k -> map f (m k))
instance (forall f. c f => Map f) => Strong (Bazaar c a b) where
  strong a = \(Bazaar m) -> Bazaar (\k -> map (a,) (m k))
instance (forall f. c f => Map f) => Remap (Bazaar c a b) where
  remap _ f (Bazaar m) = Bazaar (\k -> map f (m k))
instance (c (Bazaar c a b), forall f. c f => (Map f, Pure f)) => Pure (Bazaar c a b) where
  pure t = Bazaar (\_ ->  pure t)
instance {-# Overlappable #-} Remap f => Coercemap f where coercemap f !x = remap coerce f x
instance {-# Overlappable #-} Promap p => Coercepromap p where
  coercepromap _ _ !p = promap coerce coerce p
-- |A @Pure f@ distributes through Sum types:
--  http://r6research.livejournal.com/28338.html
instance {-# Overlappable #-} (Pure t, Zero x) => One (t x) where one = pure zero

-- * IsEither
type family LeftF t where LeftF (E a) = a
class (Map f, f ~ E (LeftF f)) => IsEither f
instance IsEither (E a)

type family Left t where Left (E a b) = a
type family Right t where Right (E a b) = b
class a ~ E (Left a) (Right a) => IsEither' a
instance a ~ E (Left a) (Right a) => IsEither' a

-- * Impl
{-instance Impl Postmap where-}
  {-type Methods Postmap = '["postmap"]-}
  {-impl p (Arg postmap) = [d|-}
    {-instance Postmap $p where postmap  = $postmap-}
    {-instance Map    ($p [tv|x|]) where map      = $postmap-}
    {-instance Strong ($p [tv|x|]) where strong a = $postmap ((,) a)-}
    {-instance Remap  ($p [tv|x|]) where remap _  = $postmap-}
   {-|]-}
{-instance Impl Strong where-}
  {-type Methods Strong = '["remap", "strong"]-}
  {-impl f (Arg remap) (Arg strong) = [d|-}
    {-instance Remap  $f where remap  = $remap-}
    {-instance Strong $f where strong = $strong-}
   {-|]-}
{-instance Impl Premap where-}
  {-type Methods Premap = '["premap"]-}
  {-impl p (Arg premap) = [d|instance Premap $p where premap  = $premap|]-}
{-instance Impl Promap where-}
  {-type Methods Promap = '["promap"]-}
  {-impl p (Arg promap) = [d|-}
    {-instance Promap  $p where promap   = $promap-}
    {-instance Premap  $p where premap f = $promap f \ x -> x-}
    {-instance Postmap $p where postmap  = $promap \ x -> x-}
    {-instance Map    ($p [tv|x|]) where map      = postmap-}
    {-instance Strong ($p [tv|x|]) where strong a = map ((,) a)-}
    {-instance Remap  ($p [tv|x|]) where remap _  = map-}
   {-|]-}
{-instance Impl Pure where-}
  {-type Methods Pure = '["remap", "pure"]-}
  {-impl f (arg #remap -> r) (arg #pure -> p) = [d|-}
    {-instance Pure   $f where pure = $p-}
    {-instance Remap  $f where remap _  = $r-}
   {-|]-}
{-instance Impl Map where-}
  {-type Methods Map = '["map"]-}
  {-impl f (Arg map) = [d|-}
    {-instance Map    $f where map      = $map-}
    {-instance Strong $f where strong a = $map ((,) a)-}
    {-instance Remap  $f where remap _  = $map-}
   {-|]-}
{-instance Impl Remap where-}
  {-type Methods Remap = '["remap"]-}
  {-impl f (Arg remap) = [d|instance Remap $f where remap = $remap|]-}

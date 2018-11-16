{-# language QuasiQuotes #-}
{-# language ImpredicativeTypes #-}
{-# language EmptyCase #-}
{-# language UndecidableSuperClasses #-}
{-# language DefaultSignatures #-}
{-# language FlexibleContexts #-}
{-# language InstanceSigs #-}
{-# language UndecidableInstances #-}
{-# language TemplateHaskell #-}
module Traverse where
import GHC.Types
import Promap
import Impl
import TV
import qualified Prelude as P
import Choice
import Applicative
import Bazaar
import E
import I
import O
import Unsafe.Coerce
import Data.Proxy
import Types

import Coerce

class Either' f  where rep :: Proxy f
instance f ~ E x => Either' f

type Either x = ((~) (E x))

impl @Map    [t|((,) [tv|a|])|]  ! #map    [|\f (a,b) -> (a, f b)|]

class Map t => Traverse c t | t -> c where
  traverse :: c f => (a -> f b) -> t a -> f (t b)
  traverse afb ta = sequence (map afb ta)
  sequence :: c f => t (f a) -> f (t a)
  sequence = traverse \ x -> x

cocollect :: forall c f t a b. (Traverse c t, forall ff. c ff => Map ff, c f)
          => (t a -> b) -> t (f a) -> f b
cocollect tab tfa = map tab (sequence @c tfa)


{-instance (c (Baz c t b), forall ff bb aa. c ff => (Map ff, c (O ff (Bazaar c bb aa)))) => Traverse c (Baz c t b) where-}

class Promap p => Traversed (c :: (* -> *) -> Constraint) p | p -> c where
  traversal :: (forall f. c f => (a -> f b) -> s -> f t) -> p a b -> p s t
  default traversal :: (forall ff bb aa. c ff => (Map ff, c (O ff (Bazaar c bb aa))), c I, c (Baz c t b)) => (forall f. c f => (a -> f b) -> s -> f t) -> p a b -> p s t
  traversal f pab = promap (\s -> Baz (\afb -> f afb s)) (sold @c) (traversed pab)
  traversed :: Traverse c t => p a b -> p (t a) (t b)
  traversed = traversal @c (traverse @c)

_2 :: Traversed Map p => p a b -> p (x,a) (x,b)
_2 = traversed
_1 :: Traversed Map p => p a b -> p (a,x) (b,x)
_1 p = let swap (a,b) = (b,a) in promap swap swap (_2 p)

lens :: Traversed Map p => (s -> a) -> (s -> b -> t) -> p a b -> p s t
lens get set = traversal \ afb s -> set s `map` afb (get s)

lens0 :: (Choice p, Traversed Map p) => (s -> E t a) -> (s -> b -> t) -> p a b -> p s t
lens0 get set pab = promap (\s -> (get s, s)) (\(bt,s) -> case bt of {L t -> t; R b -> set s b}) (_1 (_R pab))


{-grate f = \p -> promap (\a g -> g a) f (zipping zip p)-}
class Promap p => Closed p where
  grate :: (((s -> a) -> b) -> t) -> p a b -> p s t
  {-grate f = \p -> promap (\a g -> g a) f (zipping zip p)-}
  zipping :: (forall f. Map f => (f a -> b) -> f s -> t) -> p a b -> p s t
  zipping sabsst = grate (`sabsst` \x -> x)



instance Traverse Map ((,) x) where traverse f (x,a) = map (x,) (f a)

instance Traverse Applicative [] where
  traverse f = go where
    go = \case
      [] -> pure []
      a : as -> (:) `map` f a `ap` go as
{-traverse0 = traverse @Pure @-}



instance Traversed Map (->) where traversal l f s = case l (\a -> I (f a)) s of {I t -> t} 
{-instance Traversed Pure (->) where traversal l f s = case l (\a -> I (f a)) s of {I t -> t} -}



{-instance  Traverse (Baz c t b) where-}
  {-type TraverseC (Baz c t b) = c-}
  {-traverse f (Baz bz) = map (\(Bazaar m) -> Baz m) ((\(O fg) -> fg) (bz (\x -> O (map (sell @Map) (f x)))))-}



instance (c (Baz c t b), forall ff bb aa. c ff => (Map ff, c (O ff (Bazaar c bb aa)))) => Traverse c (Baz c t b) where
  traverse f (Baz bz) = map Baz_ (unO (bz (\x -> O (map (sell @c) (f x)))))


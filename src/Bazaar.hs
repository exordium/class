{-# language UndecidableInstances #-}
{-# language TemplateHaskell #-}
{-# language QuasiQuotes #-}
module Bazaar where
import GHC.Types
import I
import O
import Applicative
import Impl
import TV

newtype Baz (c :: (* -> *) -> Constraint) t b a = Baz_ (Bazaar c a b t)
instance Map (Baz c t b) where map xy (Baz xfbft) = Baz (\yfb -> xfbft (\x -> yfb (xy x)))
instance Remap (Baz c t b) where remap _ = map
instance Strong (Baz c t b) where strong x (Baz afbft) = Baz (\xafb -> afbft (\a -> xafb (x,a)))

pattern Baz f = Baz_ (Bazaar f)
runBaz (Baz f) = f

sold :: forall c t a. c I => Baz c t a a -> t
sold (Baz afaft) = case afaft I of I t -> t

newtype Bazaar (c :: (* -> *) -> Constraint) a b t = Bazaar {runBazaar :: forall f. c f => (a -> f b) -> f t}
sell :: forall c a b. a -> Bazaar c a b b
sell a = Bazaar (\f -> f a)

instance (c (Bazaar c a b), forall f. c f => Map f) => Map (Bazaar c a b) where
  map f (Bazaar m) = Bazaar (\k -> map f (m k))
instance (forall f. c f => Map f) => Strong (Bazaar c a b) where
  strong a = \(Bazaar m) -> Bazaar (\k -> map (a,) (m k))
instance (forall f. c f => Map f) => Remap (Bazaar c a b) where
  remap _ f (Bazaar m) = Bazaar (\k -> map f (m k))
instance (c (Bazaar c a b), forall f. c f => Pure f) => Pure (Bazaar c a b) where
  pure t = Bazaar (\_ ->  pure t)

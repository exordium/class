module Type.Bazaar where
import GHC.Types
import Type.I
import Type.O
import Type.K

newtype Baz (c :: (* -> *) -> Constraint) t b a = Baz_ (Bazaar c a b t)

pattern Baz f = Baz_ (Bazaar f); {-# complete Baz #-}
runBaz (Baz f) = f

sold :: forall c t a. c I => Baz c t a a -> t
sold (Baz afaft) = case afaft I of I t -> t

newtype Bazaar (c :: (* -> *) -> Constraint) a b t = Bazaar
  {runBazaar :: forall f. c f => (a -> f b) -> f t}
sell :: forall c a b. a -> Bazaar c a b b
sell a = Bazaar \ f -> f a
buy :: forall c a b. c (K a) => Bazaar c a b b -> a
buy (Bazaar f) = unK (f K)

{-# language MagicHash #-}
module Type.Bazaar where
import GHC.Types
import Type.I
import Type.K
import Functor
import Types
import Fun (coerce#)

-- * @Baz@
newtype Baz (c :: (* -> *) -> Constraint) t b a = Baz_ (Bazaar c a b t)

pattern Baz f = Baz_ (Bazaar f); {-# complete Baz #-}
runBaz (Baz f) = f

sold :: forall c t a. c I => Baz c t a a -> t
sold (Baz afaft) = case afaft I of I t -> t

-- * @Bazaar@
newtype Bazaar (c :: (* -> *) -> Constraint) a b t = Bazaar
  {runBazaar :: forall f. c f => (a -> f b) -> f t}
sell :: forall c a b. a -> Bazaar c a b b
sell a = Bazaar \ f -> f a
buy :: forall c a b. c (K a) => Bazaar c a b b -> a
buy (Bazaar f) = unK (f K)
--
-- * @O@
newtype O (f :: * -> *) (g :: * -> *) a = O {unO :: f (g a)}
instance ((Representational & Map) f, (Representational & Map) g) => Map (O f g)
  where map f (O fg) = O (map f $@ fg)
instance (Representational f, Representational g) => Map_ (O f g)
  where map_ _ = coerce#
{-deriving via Remap ## O f g instance (Remap f, Remap g) => Map_ (O f g)-}
instance ((Representational & Remap) f, (Representational & Remap) g) => Remap (O f g)
  where remap f g (O fg) = O (remap (remap g f) (remap f g) fg)
instance ((Traverses c & Representational) f
         ,(Traverses c & Representational) g
         ,c ==> Map_) => Traverses c (O f g) where
  traverses f (O fg) = O #@ traverses @c (traverses @c f) fg

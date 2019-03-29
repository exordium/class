{-# language MagicHash #-}
module Type.Bazaar where
import GHC.Types
import Type.I
import Type.K
import Functor
import Types (type (==>))
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
instance (Representational f, Map f, Representational g, Map g) => Map (O f g)
  where map f (O fg) = O (map f $@ fg)
instance (Representational f, Representational g) => MapRep (O f g)
  where mapRep _ = coerce#
{-deriving via Remap ## O f g instance (Remap f, Remap g) => MapRep (O f g)-}
instance (Representational f, Remap f, Representational g, Remap g) => Remap (O f g)
  where remap f g (O fg) = O (remap (remap g f) (remap f g) fg)
instance (TraverseC c f, Representational f
         ,TraverseC c g, Representational g
         ,c ==> MapRep) => TraverseC c (O f g) where
  traverseC f (O fg) = O #@ traverseC @c (traverseC @c f) fg

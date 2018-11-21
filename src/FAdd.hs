module FAdd where
import Map
import E
import FDot
import Fun
import Add

class (forall x. Add (f x), Monoidal E f, Map f) => FAdd f where
  fadd :: f a -> f a -> f a
  fadd fa fa' = map (id ||| id) (monoidal fa fa')

instance FAdd []

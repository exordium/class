module Def where
import K
import qualified Prelude as P

class Def a where def :: a
instance Def () where def = ()
instance Def [a] where def = []
instance Def (P.Maybe a) where def = P.Nothing
instance Def a => Def (K a b) where def = K def

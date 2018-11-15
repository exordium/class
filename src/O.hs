module O where
import Map

newtype O f g a = O {unO :: f (g a)}
instance (Map f, Map g) => Map (O f g) where map f (O fg) = O (map (map f) fg)
instance (Remap f, Remap g) => Remap (O f g) where remap f g (O fg) = O (remap (remap g f) (remap f g) fg)
instance (Map f, Strong g) => Strong (O f g) where strong a (O fg) = O (map (strong a) fg)

{-# language UndecidableInstances #-}
{-# language TemplateHaskell #-}
module Remap (Remap(..), module X) where
import qualified Prelude as P
import Impl as X hiding ((!))
import E
import Coercemap
import Coerce

class Coercemap f => Remap f where remap :: (b -> a) -> (a -> b) -> f a -> f b

instance Impl Remap where
  type Methods Remap = '["remap"]
  impl f (Arg remap) = [d|instance Remap $f where remap = $remap|]

instance Remap [] where remap _ = P.map
instance Remap ((->) x) where remap _ f g = \a ->  f (g a)
instance Remap (E x) where remap _ f = \case {L x -> L x; R a -> R (f a)}

instance {-# Overlappable #-} Remap f => Coercemap f where coercemap f !x = remap coerce f x

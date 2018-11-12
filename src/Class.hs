{-# language UndecidableInstances #-}
module Class (module Class, module X) where
import Prelude ()
import Data.Coerce
import Promap as X
import Bimap as X
import Comap as X

{-instance Coercible1 Foo []-}

{-instance {-# Overlappable #-} Postmap f => Map (f x) where map = postmap-}

class (forall x. Comap (f x)) => Copostmap f where
  copostmap :: (a -> b) -> f x b -> f x a
{-instance {-# Overlappable #-} Copostmap f => Comap (f x) where comap = copostmap-}



{-instance Remap ((->) x) where-}
  {-remap _ f p = \a -> f (p a)-}
{-instance Remap [] where-}
  {-remap _ f = go where-}
    {-go = \case-}
      {-[] -> []-}
      {-a:as -> f a : go as-}


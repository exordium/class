{-# language MagicHash #-}
{-# language StandaloneDeriving #-}
{-# language DeriveAnyClass #-}
{-# language DefaultSignatures #-}
{-# language RoleAnnotations #-}
{-# language UndecidableInstances #-}
module Coerce where
  {-(type (=#)-}
  {-,coerce-}
  {-,module X) where-}
import GHC.Types as X (Coercible)
import qualified GHC.Prim as GHC (coerce)
import Map

import qualified Prelude as P
 
-- | Representational equality
type (=#) = Coercible
coerce :: b =# a => a -> b
coerce = GHC.coerce; {-# INLINE coerce #-}

-- | Representational Equality on functors
class    (forall a. f a =# g a) => Coercible1 f g
instance (forall a. f a =# g a) => Coercible1 f g
type (#=#) = Coercible1
coerce1 :: forall g f a. f #=# g => f a -> g a
coerce1 = GHC.coerce @(f a) @(g a)

-- | 'Representational' types. 
class    ((forall a b. a =# b => f a =# f b),Coercemap f) => Representational f
instance ((forall a b. a =# b => f a =# f b),Coercemap f) => Representational f
representational :: (b =# a, Representational f) => f a -> f b
{-# INLINE representational #-}
representational = GHC.coerce

-- | 'Phantom' types can ignore their type parameter. Instances are automatically provided by GHC
class    ((forall x y. f x =# f y)) => Phantom f
instance ((forall x y. f x =# f y)) => Phantom f
phantom :: forall b a f. Phantom f => f a -> f b
phantom = GHC.coerce @(f a) @(f b); {-# INLINE phantom #-}

class Coercemap f where
  coercemap :: a =# b => (a -> b) -> f a -> f b
  default coercemap :: (Representational f, a =# b) => (a -> b) -> f a -> f b
  coercemap _ = coerce
  {-# INLINE coercemap #-}
  {-coercemap f !x = map f x-}
instance {-# Overlappable #-} Remap f => Coercemap f where coercemap f !x = remap coerce f x

{-newtype I = I P.Int-}
{-data Foob a = Foob a-}
{-{-type role Foob nominal-}-}

{-impl @Map [t|Foob|] ! #map [|\f (Foob a) -> Foob (f a)|]-}
{-instance Coercemap Foob-}

{-xxx :: Foob P.Int -> Foob I-}
{-xxx = coercemap I  -}

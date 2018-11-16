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
import {-# source #-} Coercemap

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
coerce1 = GHC.coerce

-- | 'Representational' types. 
class    ((forall a b. a =# b => f a =# f b),Coercemap f) => Representational f
instance ((forall a b. a =# b => f a =# f b),Coercemap f) => Representational f
representational :: forall b a f. (a =# b, Representational f) => f a -> f b
{-# INLINE representational #-}
representational = GHC.coerce

-- | 'Phantom' types can ignore their type parameter. Instances are automatically provided by GHC
class    ((forall x y. f x =# f y)) => Phantom f
instance ((forall x y. f x =# f y)) => Phantom f
phantom :: forall b a f. Phantom f => f a -> f b
phantom = GHC.coerce @(f a) @(f b); {-# INLINE phantom #-}


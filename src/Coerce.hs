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


import qualified Prelude as P
 

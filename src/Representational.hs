{-# language MagicHash #-}
{-# language StandaloneDeriving #-}
{-# language DeriveAnyClass #-}
{-# language DefaultSignatures #-}
{-# language RoleAnnotations #-}
{-# language UndecidableInstances #-}
module Representational
  (Representational(..)
  ,MapCoerce,mapCoerce,map#
  ) where
import Coercible
import Map
import qualified Prelude as P
import GHC.TypeLits

map# :: (MapCoerce f, b =# a) => (a -> b) -> f a -> f b
-- | Strictly map with a function that is assumed operationally to be a cast, such as a newtype constructor. 
map# = _map#; {-# INLINE map# #-}
-- | This class embodies a static choice whether to use 'map' or 'coerce' depending on if 'f' is 'Representational'. 
class Map f => MapCoerce f where
  _map# :: a =# b => (a -> b) -> f a -> f b
  default _map# :: (Representational f, a =# b) => (a -> b) -> f a -> f b
  _map# _ = coerce
  {-# INLINE _map# #-}
  {-_map# f !x = map f x-}
instance {-# Overlappable #-} Map f => MapCoerce f where _map# f !x = map f x
{-instance {-# Overlappable #-} (Map f, Representational f) => MapCoerce f where _map# _ = coerce-}
{-newtype I = I P.Int-}
{-data Foob a = Foob a-}
{-{-type role Foob nominal-}-}

{-impl @Map [t|Foob|] ! #map [|\f (Foob a) -> Foob (f a)|]-}
{-instance MapCoerce Foob-}

{-ff :: Foob P.Int -> Foob I-}
{-ff = map# I -}

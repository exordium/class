{-# language MagicHash #-}
{-# language StandaloneDeriving #-}
{-# language DeriveAnyClass #-}
{-# language DefaultSignatures #-}
{-# language RoleAnnotations #-}
{-# language UndecidableInstances #-}
module Test where
import qualified Prelude as P
import Coerce
import Coerce.Map
import Map

newtype I = I P.Int
data Foob a = Foob a
{-type role Foob nominal-}
{-instance Container Foob-}

impl @Map [t|Foob|] ! #map [|\f (Foob x) -> Foob (f x)|]

ff :: Foob P.Int -> Foob I
ff = coercemap I

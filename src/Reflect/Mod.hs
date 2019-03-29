module Reflect.Mod where
import Reflect
import qualified Prelude as P
import qualified Data.Proxy as P

newtype Mod a (s :: *) = Mod a deriving newtype P.Num
instance (Reifies s a, P.Integral a) => P.Semigroup (Mod a s) where
  Mod a <> Mod b = Mod ((a P.+ b) `P.mod` reflect' @s)

ex3 :: P.Integral r => r
ex3 = using Mod 10 do 3 P.<> 8

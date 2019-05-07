module Reflect.Monoid (Reified(Monoid)) where
import Reflect
import qualified Prelude as P
import qualified Data.Foldable as P
import qualified Data.Proxy as P
import qualified Data.Coerce as P
import Types
import Fun

type Monoid = P.Monoid

data instance Reified Monoid a = Monoid {op :: a -> a -> a, nil :: a}

instance Reifies s (Reified Monoid a) => P.Semigroup (Instance Monoid a s) where
  Instance x <> Instance y = let m = reflect (P.Proxy @s) in Instance @Monoid (op m x y) 
instance Reifies s (Reified Monoid a) => P.Monoid (Instance Monoid a s) where
  mempty = let m = reflect (P.Proxy @s) in Instance @Monoid (nil m)
  mappend = (P.<>)

{-sum :: [Int] -> Int-}
sum :: P.Num a => [a] -> a
sum xs = usingInst add do P.fold (P.map coerce xs)

ex1 :: P.Num r => r
ex1 = using (Instance @Monoid) mul do 3 P.<> 13

ex1' :: P.Num r => r
ex1' = usingInst mul do 3 P.<> 13

--ex2 :: Int
--ex2 = usingInst Monoid{op = (P.+), nil = 0} do q 3 where
  --q :: (s ?: Monoid) Int => Int -> (s !: Monoid) Int
  --q i = Instance i P.<> 10

--ex2' :: Int
--ex2' = q 3
  --`withInst` Monoid{op = (P.+), nil = 0}
   --where
    --q :: (s ?: Monoid) Int => Int -> (s !: Monoid) Int
    --q i = Instance i P.<> 10


add :: P.Num a => Reified Monoid a
add = Monoid (P.+) 0

mul :: P.Num a => Reified Monoid a
mul = Monoid (P.*) 1

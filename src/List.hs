{-# language TemplateHaskell #-}
module List where
import qualified Prelude
import Map
import These

list'align :: [a] -> [b] -> [These a b]
list'align [] bs = map That bs
list'align as [] = map This as
list'align (a:as) (b:bs) = These a b : list'align as bs

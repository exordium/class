{-# language TemplateHaskell #-}
module Type.List where
import qualified Prelude
import Type.These

list'align :: [a] -> [b] -> [These a b]
list'align [] bs = Prelude.map That bs
list'align as [] = Prelude.map This as
list'align (a:as) (b:bs) = These a b : list'align as bs

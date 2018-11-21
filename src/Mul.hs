module Mul where

class One a where one :: a
class Mul a where mul :: a -> a -> a
class (One a, Mul a) => Mul1 a

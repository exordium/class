{-# language UndecidableInstances #-}
module Copostmap (module Copostmap, module X) where
import Comap as X

class (forall x. Comap (f x)) => Copostmap f where copostmap :: (a -> b) -> f x b -> f x a

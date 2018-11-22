{-# language TemplateHaskell #-}
module Premap (Premap(..), module X) where
import Impl as X hiding ((!))


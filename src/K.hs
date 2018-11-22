{-# language TemplateHaskell,QuasiQuotes #-}
module K where
import Impl
import TV
import Map

newtype K a b = K {unK :: a}

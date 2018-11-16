{-# language TemplateHaskell,QuasiQuotes #-}
module K where
import Impl
import TV
import Map

newtype K a b = K a
impl @Map [t|K [tv|a|]|] ! #map [|\f (K a) -> K a|]

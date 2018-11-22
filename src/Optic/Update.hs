{-# language TemplateHaskell,QuasiQuotes #-}
{-# language UndecidableInstances #-}
module Optic.Update where

set :: ((a -> b) -> s -> t) -> b -> s -> t
set l b s = l (\_ -> b) s

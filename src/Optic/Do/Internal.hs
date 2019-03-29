{-# language TemplateHaskell, QuasiQuotes #-}
module Optic.Do.Internal where
{-import Functor.Applicative-}
import Fun hiding ((!))

{-instance Apply f => FTimes (FK f a) where ftimes = ap_ftimes-}
{-instance Apply f => Apply (FK f a) where-}
  {-ap (FK fa) (FK fb) = FK ((\_ b -> b) `map` fa `ap` fb)-}
{-instance (Pure f, Zero a) => Pure (FK f a) where pure !_ = FK (pure zero)-}
{-instance (Applicative f, Zero a) => Applicative (FK f a)-}


{-newtype WrapF f a = WrapF {unwrapF :: f a}-}
{-instance (Pure f, Zero a) => Zero (WrapF f a) where zero = WrapF (pure zero)-}
{-instance (Apply f, Add a) => Add (WrapF f a) where add (WrapF a) (WrapF b) = WrapF (add `map` a `ap`     b)-}
{-instance (Applicative f, Add0 a) => Add0 (WrapF f a)-}
                                                       

{-# language TemplateHaskell, QuasiQuotes #-}
{-# language UndecidableInstances #-}
module Optic.Review where
import Impl
import TV
import K
import Promap
import Traverse
import Fun hiding ((!))

newtype Review a b = Review {runReview :: b}
impl @Promap [t|Review|] ! #promap [|\_ g (Review b) -> Review (g b)|]

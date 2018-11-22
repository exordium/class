{-# language TemplateHaskell, QuasiQuotes #-}
{-# language UndecidableInstances #-}
module Optic.Do where
import Impl
import TV
import K
import Promap
import Coercepromap
import Traverse
import Fun hiding ((!))
import Optic.Do.Internal
import Add

newtype Do f (r :: *) a (b :: *) = Do {runDo :: a -> f r}
_Do_ :: Coercepromap p => p (Do f r a b) (Do g r' s t) -> p (a -> f r) (s -> g r')
_Do_ = coercepromap Do runDo

-- | Ex: @doWith _1 print :: (Zero r, Show a) => (a,x) -> IO r
doWith :: (Zero r, Map f) => (Do (FK f x) r a b -> Do (FK f x) r s t) -> (a -> f x) -> s -> f r
doWith l afx = case l (Do (\a -> FK (afx a))) of
  Do sfkx -> \s -> case sfkx s of FK fx -> constMap zero fx

impl @Promap [t|Do [tv|f|] [tv|r|]|] ! #promap [|\f _ (Do b) -> Do (premap f b)|]
instance c (K (f r)) => Traversal c (Do f r) where
  traversal afbsft (Do afr) = Do (unK < (afbsft (K < afr)))

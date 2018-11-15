{-# language TemplateHaskell,QuasiQuotes #-}
module Optic.Update where
import Traverse
import Promap
import Impl
import TV

newtype Update b s t = Update {runUpdate :: b -> s -> t}
impl @Promap [t|Update [tv|b|]|] ! #promap [|\sa bt (Update xab) -> Update (\x s -> bt (xab x (sa s)))|]

instance Traversed Map (Update x) where
  {-traversal afbsft (Update xab) = Update (\x s -> case afbsft (\a -> I (xab x a)) s of I t -> t)-}
  traversed (Update xab) = Update (\x ta -> map (xab x) ta)

_Update :: Promap p => p (Update b a b) (Update b s t) -> p (b -> a -> b) (b -> s -> t)
_Update = promap Update runUpdate

set :: (Update b a b -> Update b s t) -> b -> s -> t
set l = promap Update runUpdate l (\b _ -> b)

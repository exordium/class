{-# language TemplateHaskell,QuasiQuotes #-}
{-# language UndecidableInstances #-}
{-module Optic.Update where-}
{-import Traverse-}
{-import Promap-}
{-import Coercepromap-}
{-import Impl-}
{-import TV-}
{-import I-}
{-import Types-}
{-import Closed-}
{-import Fun hiding ((!))-}

{-newtype Update b s t = Update {runUpdate :: b -> s -> t}-}
{-impl @Promap [t|Update [tv|b|]|] ! #promap [|\sa bt (Update xab) -> Update (\x s -> bt (xab x (sa s)))|]-}

{-instance c I => Traversal c (Update x) where-}
  {-traversal afbsft (Update xab) = Update (\x s -> case afbsft (\a -> I (xab x a)) s of I t -> t)-}
  {-{-traversed (Update xab) = Update (\x ta -> map (xab x) ta)-}-}
{-instance (c ==> Map) => Distributed c (Update x) where-}
  {-distributed (Update xab) = Update (map < xab)-}

{-_Update_ :: Coercepromap p => p (Update b a b) (Update b s t) -> p (b -> a -> b) (b -> s -> t)-}
{-_Update_ = coercepromap Update runUpdate-}

{--- | :: Setter s t a b -> b -> s -> t-}
{-set :: (Update b a b -> Update b s t) -> b -> s -> t-}
{-set l = _Update_ l (\b _ -> b)-}

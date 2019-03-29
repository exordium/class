{-# language UndecidableInstances #-}
module Reflect (Reifies(..), Reified, Instance(..), reify,using,usingInst,withInst,reflect', type (?:), type (!:)) where
import qualified Unsafe.Coerce as P
import qualified Data.Proxy as P
import qualified Prelude as P
import qualified Data.Coerce as P
import Fun
import Types
{-import Data (coerce, type (=#))-}

class Reifies s a | s -> a where reflect :: proxy s -> a
newtype Magic a r = Magic (forall (s :: *). Reifies s a => P.Proxy s -> r)

reify :: forall a r. a -> (forall (s :: *). Reifies s a => P.Proxy s -> r) -> r
reify a k = P.unsafeCoerce (Magic k :: Magic a r) (a!) P.Proxy

using :: forall a f r. (forall s. r =# f s)
      => (forall s. r -> f s) -> a
      -> (forall (s :: *). Reifies s a => f s) -> r
using _ a k = reify a (coerce @r < at k)

usingInst :: forall a c f r. Reified c r
          -> (forall (s :: *). Reifies s (Reified c r) => Instance c r s)
          -> r
usingInst a k = reify a (coerce @r < at k)

withInst :: forall a c f r. (forall (s :: *). Reifies s (Reified c r) => Instance c r s) -> Reified c r -> r
withInst k a = usingInst a k

reflect' :: forall s a. Reifies s a => a
reflect' = reflect (P.Proxy @s)

{-un :: forall s a . P.Proxy s -> Instance Monoid a s -> a-}
{-un _ (Instance Monoid a) = a-}
at :: f s -> P.Proxy s -> f s
at f _ = f


{-withMonoid :: ("op" :! (a -> a -> a)) -> ("nil" :! a) -> (forall s. Reifies s (Reified Monoid a) => Instance Monoid a s) -> a-}
{-withMonoid (arg #op -> f) (arg #nil -> z) v = reify (Reified Monoid f z) (un < at v)-}

data family Reified (c :: * -> Constraint) :: * -> *
type (s ?: c) a = Reifies s (Reified c a)
type (s !: c) a = Instance c a s
newtype Instance (c :: * -> Constraint) a (s :: *) = Instance a deriving newtype P.Num


type c ?=> a = forall s. (s ?: c) a => (s !: c) a

{-# language UndecidableInstances #-}
-- TODO: This hangs compiler when the (c ==> _) constraint fails
module Mono (fold,sum,sum1,prod,prod1,Mono.map,Mono.traverse,Each(..)) where
import qualified Data.Set as Set
import qualified Prelude as P
import Control
import Types
import Optic
import Data
import Fun
import Functor

class Each c s t a b | s -> a, t -> b, s b -> t, t a -> s where
  each :: Traversed c p => p a b -> p s t
  default each :: (Traverse c g, s ~ g a, t ~ g b, Traversed c p) => p a b -> p s t
  each = traversed @c

fold :: forall c s t a b n. (c n, Each (IsK c) s t a b) => (a -> n) -> s -> n
fold = _View_ $ each @(IsK c) @s @t

sum :: forall s t a b n. (Add0 n, Each (IsK Add0) s t a b) => (a -> n) -> s -> n
sum = fold @Add0 @s @t

sum1 :: forall s t a b n. (Add n, Each (IsK Add) s t a b) => (a -> n) -> s -> n
sum1 = fold @Add @s @t

prod :: forall s t a b n. (Mul1 n, Each (IsK Mul1) s t a b) => (a -> n) -> s -> n
prod = fold @Mul1 @s @t

prod1 :: forall s t a b n. (Mul n, Each (IsK Mul) s t a b) => (a -> n) -> s -> n
prod1 = fold @Mul @s @t

map :: forall s t a b. (Each IsI s t a b) => (a -> b) -> s -> t
map = each @IsI 

traverse :: forall c s t a b f. (c ==> Map, c f, Each c s t a b)
              => (a -> f b) -> s -> f t
traverse = _Traversing_ $ each @c

setTraverse :: forall c f a b. (c ==> Map, c f, Traverse c [], P.Ord b)
            => (a -> f b) -> Set.Set a -> f (Set.Set b)
setTraverse f = promap Set.toList (Functor.map Set.fromList) (Functor.traverse @c f)

instance (c ==> Applicative, P.Ord b) => Each c (Set.Set a) (Set.Set b) a b where
  each  = traversal @c (setTraverse @c); {-# INLINE each #-}
{-# language UndecidableInstances #-}
module Fold where
import E
import IsEither
import Types
import qualified Prelude as P

import Map
import Remap


newtype Endo a = Endo {appEndo :: a -> a}

instance Zero (Endo a) where zero = Endo \ a -> a
instance Add (Endo a) where add (Endo f) (Endo g) = Endo \ a -> f (g a)
instance Add0 (Endo a)

newtype Endo0 a = Endo0 {appEndo0 :: P.Maybe a -> a}
instance Add (Endo0 a) where Endo0 f `add` Endo0 g = Endo0 \ x' -> f (P.Just (g x'))

instance Zero () where zero = ()
instance Add () where add _ _ = ()
instance Add0 ()


class (forall x. Add x => Mul (t x)) => App t where app :: (a -> b -> r) -> t a -> t b -> t r
instance {-# Overlappable #-} (App t, Add x) => Mul (t x) where mul = app add
instance App [] where app f as bs = f P.<$> as P.<*> bs

class (forall x. Add (t x),FDot E t, Map t) => FAdd t where fadd :: t a -> t a -> t a
instance FAdd [] where fadd = (P.++)
instance {-# Overlappable #-} FAdd t => Add (t x) where add = fadd
instance FDot E [] where fdot fa fa' = fadd (map L fa) (map R fa')


class (forall x. c (t x)) => FoldMap c t where
  foldMap :: c m => (a -> m) -> t a -> m

instance (forall x. c [x], c ==> Add0) => FoldMap c [] where
  foldMap f = go where
    go = \case
      [] -> zero
      a : as -> f a `add` go as

foldr :: FoldMap Add0 t => (a -> b -> b) -> b -> t a -> b
foldr c z t = foldMap @Add0 (\x -> Endo (c x)) t `appEndo` z 

foldl :: FoldMap Add0 t => (b -> a -> b) -> b -> t a -> b
foldl bab b0 t = foldr (\a k b -> k P.$! bab b a) (\b -> b) t b0

fold :: forall c m t. (c m, FoldMap c t) => t m -> m
fold = foldMap @c \ m -> m

foldr0 :: FoldMap Zero t => (a -> b) -> b -> t a -> b
foldr0 f z t = foldMap @Zero (\x -> Endo (\_ -> f x)) t `appEndo` z

data X

foldr' :: FoldMap IsEither' t => (a -> b) -> (t X -> b) -> t a -> b
foldr' f z t  = case foldMap @IsEither' R t of
  L tx -> z tx
  R b -> f b

foldr1 :: FoldMap Add t => (a -> b -> b) -> (a -> b) -> t a -> b
foldr1 c z t = foldMap @Add (\a -> Endo0 (c' a)) t `appEndo0` P.Nothing where
  c' a = \case
    P.Nothing -> z a
    P.Just b -> c a b

foldl1 :: FoldMap Add t => (b -> a -> b) -> (a -> b) -> t a -> b
foldl1 c z t = foldMap @Add (\a -> Endo0 (c' a)) t `appEndo0` P.Nothing where
  c' a = \case
    P.Nothing -> z a
    P.Just !b -> c b a

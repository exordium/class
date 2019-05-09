{-# language MagicHash #-}
module Type.Bazaar where
import GHC.Types
import Type.I
import Type.K
import Functor
import Types
import Fun (coerce#, (<), (!))
{-
 -
 --- * @Baz@
 -newtype Baz (c :: (* -> *) -> Constraint) t b a = Baz_ (Bazaar c a b t)
 -
 -pattern Baz f = Baz_ (Bazaar f); {-# complete Baz #-}
 -runBaz (Baz f) = f
 -
 -sold :: forall c t a. c I => Baz c t a a -> t
 -sold (Baz afaft) = case afaft I of I t -> t
 -
 --- * @Bazaar@
 -newtype Bazaar (c :: (* -> *) -> Constraint) a b t = Bazaar
 -  {runBazaar :: forall f. c f => (a -> f b) -> f t}
 -sell :: forall c a b. a -> Bazaar c a b b
 -sell a = Bazaar \ f -> f a
 -buy :: forall c a b. c (K a) => Bazaar c a b b -> a
 -buy (Bazaar f) = unK (f K)
 -
 -deriving via (Representational ## Baz c t b) instance Map_ (Baz c t b)
 -deriving via (Map ## Baz c t b) instance Remap (Baz c t b)
 -instance Map (Baz c t b) where
 -  map xy (Baz xfbft) = Baz \ yfb -> xfbft \ x -> yfb (xy x)
 ---
 --- * @O@
 -newtype O (f :: * -> *) (g :: * -> *) a = O {unO :: f (g a)}
 -instance (Representational f, Applicative f, Representational g, Applicative g)
 -  => Applicative (O f g)
 -instance (Representational f, Pure f, Representational g, Pure g) => Pure (O f g)
 -  where pure a = O (pure (pure a))
 -deriving via (Apply ## O f g) instance
 -  (Representational f, Apply f, Representational g, Apply g) => Monoidal (,) (O f g)
 -instance (Representational f, Apply f, Representational g, Apply g) => Apply (O f g)
 -    where ap (O f) (O a) = O (liftA2 ap f a)
 -instance ((Representational & Map) f, (Representational & Map) g) => Map (O f g)
 -  where map f (O fg) = O (map f $@ fg)
 -instance (Representational f, Representational g) => Map_ (O f g) where mapAs = coerce#
 -{-deriving via Remap ## O f g instance (Remap f, Remap g) => Map_ (O f g)-}
 -instance (Representational f, Remap f, Representational g, Remap g) => Remap (O f g)
 -  where remap f g (O fg) = O (remap (remap g f) (remap f g) fg)
 -instance ((Traverses c & Representational) f
 -         ,(Traverses c & Representational) g
 -         ,c ==> Map_) => Traverses c (O f g) where
 -  traverses f (O fg) = O #@ traverses @c (traverses @c f) fg
 -
 -instance (forall f x. c (O f (Bazaar c x b)), forall x. c (K x), c ==> Remap)
 -  => Traverses c (Baz c t b) where
 -     traverses f (Baz bz) = map_ Baz_ (unO (bz (\x -> O (remap buy (sell @c) (f x)))))
 -
 -instance (c ==> Map, c (Bazaar c a b)) => Map (Bazaar c a b) where
 -  map f (Bazaar m) = Bazaar (\afb -> map f (m afb))
 -  {-map f (Bazaar m) = Bazaar (map f < m)-}
 -instance c ==> Map_ => Map_ (Bazaar c a b) where mapAs (Bazaar m) = Bazaar (mapAs < m)
 -instance c ==> Remap => Remap (Bazaar c a b) where
 -  remap f g (Bazaar m) = Bazaar (\k -> remap f g (m k))
 -instance (c (Bazaar c a b), c ==> Pure) => Pure (Bazaar c a b) where
 -  pure t = Bazaar (pure t!)
 -
 -instance (c (Bazaar c a b), c ==> Apply) => Apply (Bazaar c a b) where
 -  Bazaar afbfxy `ap` Bazaar afbfx = Bazaar \ afb -> afbfxy afb |$| afbfx afb
 -instance (c (Bazaar c a b), c ==> Applicative) => Applicative (Bazaar c a b)
 -instance (c (Bazaar c a b), c ==> Monad) => Monad (Bazaar c a b) where
 -  bind abz (Bazaar xmyma) = Bazaar \ xmy ->
 -    (`bind` xmyma xmy) \ a -> case abz a of Bazaar xmymb -> xmymb xmy
 -
 -  {-
 -   -default traversal :: (forall ff bb aa. c ff => c (O ff (Bazaar c bb aa))
 -   -                     ,c I , c (Baz c t b))
 -   -                  => (forall f. c f => (a -> f b) -> s -> f t)
 -   -                  -> p a b -> p s t
 -   -traversal f pab = promap (\s -> Baz (\afb -> f afb s)) (sold @c) (traversed @c pab)
 -   -}
 -}

{-# language TemplateHaskell,QuasiQuotes #-}
module Choice (Choice(..), module E) where
import Promap as X
import Impl
import E

class Promap p => Choice p where
  {-# minimal prism | _L | _R #-}
  prism :: (s -> E t a) -> (b -> t) -> p a b -> p s t
  prism pat constr = \p -> promap (\s -> E.swap (pat s)) (\case {L a -> constr a; R x -> x}) (_L p)
  _R :: p a b -> p (E x a) (E x b)
  _R = prism (\case {L t -> L (L t); R a -> R a}) R
  _L :: p a b -> p (E a y) (E b y)
  _L = \p -> promap E.swap E.swap (_R p)

impl @Promap [t|(->)|]           ! #promap [|\f g p a -> g (p (f a))|]
instance Choice (->) where _R ab = \case {L x -> L x; R a -> R (ab a)}

{-# language EmptyCase #-}
module X where
data X
absurd :: X -> a
absurd = \case{}

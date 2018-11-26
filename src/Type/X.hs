{-# language EmptyCase #-}
module Type.X where
data X
absurd :: X -> a
absurd = \case{}

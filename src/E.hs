module E where

data E a b = L a | R b
swap = \case {L a -> R a; R b -> L b}

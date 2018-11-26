module Type.E where
import qualified Prelude as P

data E a b = L a | R b deriving (P.Show)
swap = \case {L a -> R a; R b -> L b}

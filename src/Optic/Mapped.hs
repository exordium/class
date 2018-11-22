module Mapped where
import Promap
import Pure
import Distribute
import Types
import IsEither
import qualified Prelude as P
import Fun
import Traverse
import Closed

class (Traversed ((~) I) p, Closed p) => Mapped p where
  mapped :: Map f => p a b -> p (t a) (t b)

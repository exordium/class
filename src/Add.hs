module Add where
import qualified Prelude as P

class Zero a where zero :: a
class Add a where add :: a -> a -> a
class (Zero a, Add a) => Add0 a

instance Zero [x] where zero = []
instance Add [x] where add = (P.++)

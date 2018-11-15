module I where
import qualified Prelude as P
import Applicative

newtype I a = I a deriving stock P.Show deriving anyclass Applicative
instance Apply I where ap (I f) (I a) = I (f a)
instance Pure I where pure = I
instance Map I where map f (I a) = I (f a)
instance Remap I where remap _ = map
instance Strong I where strong a (I b) = I (a,b)

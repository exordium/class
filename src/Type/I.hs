module Type.I where
import qualified Prelude as P
{-import Applicative-}

newtype I a = I {unI :: a} deriving stock P.Show
{-instance Apply I where ap (I f) (I a) = I (f a)-}
{-instance Pure I where pure = I-}

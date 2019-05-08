module FFI.Ptr where
import Data

import Foreign.Ptr
import Foreign.Ptr as X (Ptr,FunPtr)

instance Nil (Ptr a) where nil = nullPtr
instance Nil (FunPtr a) where nil = nullFunPtr


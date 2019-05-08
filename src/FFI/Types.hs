{-# language ForeignFunctionInterface, CApiFFI, UnliftedFFITypes, GHCForeignImportPrim #-}
module FFI.Types where

import Foreign.C.Types
import Types.Numeric

foreign import ccall safe "foo.c foo" foo :: I8 -> I8
foreign import ccall safe "foo.c foo" cfoo :: CChar -> CChar

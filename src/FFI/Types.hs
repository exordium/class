{-# language ForeignFunctionInterface, CApiFFI, UnliftedFFITypes, GHCForeignImportPrim #-}
module FFI.Types where
import Fun
--import Foreign.C.Types
import Types.Numeric

foreign import ccall safe "foo.c foo" foo :: I8 -> I8
bar = foo $! 3

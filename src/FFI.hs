{-# language MagicHash #-}
module FFI 
  (
  -- * Pointers
   Ptr(..) ,alignPtr
  -- ** Function Pointers
  ,FunPtr(..), freeHaskellFunPtr
  -- ** Foreign Pointers
  ,ForeignPtr(..)
  -- *** Foreign Pointer Operations
  ,newForeignPtr,addForeignPtrFinalizer,finalizeForeignPtr
  ,withForeignPtr,touchForeignPtr
  -- *** Allocating Managed Memory
  ,mallocForeignPtr,mallocForeignPtrBytes,mallocForeignPtrArray,mallocForeignPtrArray0


  ) where
import Fun
import Fun.Cast
import Foreign.C
import Foreign.ForeignPtr hiding (newForeignPtr,addForeignPtrFinalizer)
import qualified Foreign.ForeignPtr as GHC
import qualified Foreign.Concurrent as GHC.Conc
import qualified Named
import qualified Named.Internal as Named
import qualified Prelude as P
import Data
import Types.Numeric
import Foreign.Ptr (freeHaskellFunPtr)
import GHC.Ptr hiding (alignPtr)
import qualified GHC.Ptr as GHC
import qualified GHC.Prim as GHC

-- = [FFI](https://www.haskell.org/onlinereport/haskell2010/haskellch8.html)

-- * [FFI Imports](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/ffi-chap.html#foreign-function-interface-ffi)
--
-- ** Calling Conventions

-- $ccall
--
-- $unsafe
-- === [Unsafe 
--
-- @unsafe@ calls guarentee that:
--
-- * Garbage collection will never occur until an @unsafe@ returns
-- * @unsafe@ calls will be performed on the same thread they are called from.
--
-- $prim
-- === [Primitive imports](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/ffi-chap.html#primitive-imports)
-- @foreign import prim "foo" foo :: ByteArray\# -> (\# Int\#, Int\# \#)@
--
-- Import functions written in [Cmm code](https://gitlab.haskell.org/ghc/ghc/wikis/commentary/rts/cmm) using the [internal GHC calling convention](https://gitlab.haskell.org/ghc/ghc/wikis/commentary/prim-ops).
-- The arguments and results must be unboxed types, or 'Any'
--

-- $interruptible
-- === [Interruptible Foreign Calls](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/ffi-chap.html#interruptible-foreign-calls)
-- @foreign import ccall interruptible "sleep" sleepBlock :: U32 -> IO U32@
--
-- @interruptible@ behaves exactly as @safe@, except that when a 'throwTo' is
-- directed at a thread in an interruptible foreign call,
-- the thread making the foreign call is sent a @SIGPIPE@ signal using @pthread_kill()@.
-- This is usually enough to cause a blocking system call to return with @EINTR@
-- (GHC by default installs an empty signal handler for @SIGPIPE@, to override the
-- default behaviour which is to terminate the process immediately).
--
-- Normally when the target of a throwTo is involved in a foreign call, the exception
-- is not raised until the call returns, and in the meantime the caller is blocked.
-- This can result in unresponsiveness, which is particularly undesirable in the case of
-- user interrupt (e.g. Control-C). The default behaviour when a Control-C signal is
-- received (@SIGINT@ on Unix) is to raise the @UserInterrupt@ exception in the
-- main thread; if the main thread is blocked in a foreign call at the time, then the
-- program will not respond to the user interrupt.

-- $capi
-- === [The CAPI calling convention](https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/ffi-chap.html#the-capi-calling-convention)
-- @foreign import capi "header.h f_possibly_macro" foo :: I32 -> IO I32@
--
-- @foreign import capi "pi.h value pi" c_pi :: F64@
--
-- Normally, foreign imports generate a function call using the platform's C ABI,
-- linking directly to an exposed symbol. Using @capi@ uses the C API instead, operating
-- on the source of the provided header. This means it can access @#define@ macros
-- as well as values and function calls.
--
--



-- | Turns a plain memory reference into a foreign pointer, and may associate a
-- finalizer with the reference. The finalizer will be executed after the last reference
-- to the foreign object is dropped. There is no guarantee of promptness.
-- Finalizer pointers are guarenteed to execute before the program exits, but
-- IO finalizers are not.
--
-- Finalziers can be either a 'FunPtr' reference to external finalizer code
-- (with or without additional environment), or arbitrary 'IO' actions run concurrently
-- in a seperate thread. Calls to this function are expected to use only one of these
-- methods (more finalizers can be added with 'addForeignPtrFinalizer'), and in particular,
-- @IO@ finalizers __cannot__ be used with @FunPtr@ finalizers on the same @ForeignPtr@.
--
-- Note that references from an IO finalizer follow the liveness behaviour of 'touchForeignPtr'.
newForeignPtr :: Ptr a -- ^ Plain pointer to turn into a foreign pointer by associating a finalizer.
               -> "finalizer_ptr"    :? FunPtr (Ptr a -> IO ())
               -- ^ Foreign finalizer pointer to execute when the 'ForeignPtr' goes of out scope.
               -> "finalizer_io"  :? IO ()
               -- ^ Arbitrary IO finalizer to execute when the 'ForeignPtr' goes of out scope.
               -> "finalizer_env" :? FunPtr (Ptr env -> Ptr a -> IO ())
               -- ^ Foreign finalizer pointer to execute when the 'ForeignPtr' goes of out scope.
               -> "env" :? Ptr env
               -- ^ The environment pointer to pass to the @finalizer_env@ @FunPtr@
               -> IO (GHC.ForeignPtr a)
newForeignPtr p (arg' #finalizer_ptr -> fptr)
                (arg' #finalizer_io  -> fio)
                (arg' #finalizer_env -> fenv)
                (arg' #env -> fstuff)
  = go fptr fio fenv fstuff where
  go P.Nothing  P.Nothing  P.Nothing  P.Nothing   = GHC.newForeignPtr_ p
  go (P.Just f) P.Nothing  P.Nothing  P.Nothing   = GHC.newForeignPtr f p
  go P.Nothing (P.Just f)  P.Nothing  P.Nothing   = GHC.Conc.newForeignPtr p f
  go P.Nothing  P.Nothing (P.Just f) (P.Just env) = GHC.newForeignPtrEnv f env p
  go P.Nothing P.Nothing P.Just{} P.Nothing = P.error
    "function newForeignPtr requires parameter env when called with finalizer_env"
  go P.Nothing P.Nothing P.Nothing P.Just{} = P.error
    "function newForeignPtr requires parameter finalizer_env when called with env"
  go _ _ _ _ = P.error
    "too many parameters to function newForeignPtr: valid parameters\n\
    \(finalizer_ptr | finalizer_io | finalizer_env, env)"


-- | Add a finalizer to the given foreign object created from 'newForeignPtr', to be run /before/ all other finalizers
-- currently registered on the object.
addForeignPtrFinalizer :: GHC.ForeignPtr a
                       -> "finalizer_ptr"    :? FunPtr (Ptr a -> IO ())
                       -- ^ Foreign finalizer pointer to execute when the 'ForeignPtr' goes of out scope.
                       -> "finalizer_io"  :? IO ()
                       -- ^ Arbitrary IO finalizer to execute when the 'ForeignPtr' goes of out scope.
                       -> "finalizer_env" :? FunPtr (Ptr env -> Ptr a -> IO ())
                       -- ^ Foreign finalizer pointer to execute when the 'ForeignPtr' goes of out scope.
                       -> "env" :? Ptr env
                       -- ^ The environment pointer to pass to the @finalizer_env@ @FunPtr@
                       -> IO ()
addForeignPtrFinalizer p (arg'  #finalizer_ptr -> fptr)
                          (arg' #finalizer_io  -> fio)
                          (arg' #finalizer_env -> fenv)
                          (arg' #env -> fstuff)
  = go fptr fio fenv fstuff where
  go (P.Just f) P.Nothing  P.Nothing  P.Nothing   = GHC.addForeignPtrFinalizer f p
  go P.Nothing (P.Just f)  P.Nothing  P.Nothing   = GHC.Conc.addForeignPtrFinalizer p f
  go P.Nothing  P.Nothing (P.Just f) (P.Just env) = GHC.addForeignPtrFinalizerEnv f env p
  go P.Nothing P.Nothing P.Just{} P.Nothing = P.error
    "function addForeignPtrFinalizer requires parameter env when called with finalizer_env"
  go P.Nothing P.Nothing P.Nothing P.Just{} = P.error
    "function addForeignPtrFinalizer requires parameter finalizer_env when called with env"
  go P.Nothing  P.Nothing  P.Nothing  P.Nothing = P.return ()
  go _ _ _ _ = P.error
    "too many parameters to function addForeignPtrFinalizer: valid parameters\n\
    \(finalizer_ptr | finalizer_io | finalizer_env, env)"

alignPtr :: Ptr a -> I64 -> Ptr a
alignPtr addr@(Ptr a) (I64 i) = case GHC.remAddr# a i of
  0# -> addr
  n -> Ptr (GHC.plusAddr# a (i GHC.-# n))

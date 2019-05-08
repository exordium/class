{-# language CPP #-}
module FFI.Error where
#include "HsBaseConfig.h"
import qualified Prelude as P
import qualified Foreign.Ptr as P
import qualified GHC.IO.Exception as P
import qualified System.IO.Unsafe as P
import qualified Foreign.C.String as P
import qualified Foreign.C.Types as P
import Fun (IO,Bool,($),coerce)
import Types.Numeric

-- | Haskell representation for @errno@ values.
-- The implementation deliberately exposed, to allow users to add
-- their own definition of 'Errno' values.
newtype Errno = Errno I32
instance P.Show Errno where
  show e | isValidErrno e = go e
         | P.otherwise = "(invalid errno) " P.++ go e
    where
    go EOK = "EOK"
    go E2BIG = "E2BIG"
    go EACCES = "EACCES"
    go EADDRINUSE = "EADDRINUSE"
    go EADDRNOTAVAIL = "EADDRNOTAVAIL"
    go EADV = "X"
    go EAFNOSUPPORT = "EAFNOSUPPORT"
    go EAGAIN = "EAGAIN"
    go EALREADY = "EALREADY"
    go EBADF = "EBADF"
    go EBADMSG = "EBADMSG"
    go EBADRPC = "EBADRPC"
    go EBUSY = "EBUSY"
    go ECHILD = "ECHILD"
    go ECOMM = "ECOMM"
    go ECONNABORTED = "ECONNABORTED"
    go ECONNREFUSED = "ECONNREFUSED"
    go ECONNRESET = "ECONNRESET"
    go EDEADLK = "EDEADLK"
    go EDESTADDRREQ = "EDESTADDRREQ"
    go EDIRTY = "EDIRTY"
    go EDOM = "EDOM"
    go EDQUOT = "EDQUOT"
    go EEXIST = "EEXIST"
    go EFAULT = "EFAULT"
    go EFBIG = "EFBIG"
    go EFTYPE = "EFTYPE"
    go EHOSTDOWN = "EHOSTDOWN"
    go EHOSTUNREACH = "EHOSTUNREACH"
    go EIDRM = "EIDRM"
    go EILSEQ = "EILSEQ"
    go EINPROGRESS = "EINPROGRESS"
    go EINTR = "EINTR"
    go EINVAL = "EINVAL"
    go EIO = "EIO"
    go EISCONN = "EISCONN"
    go EISDIR = "EISDIR"
    go ELOOP = "ELOOP"
    go EMFILE = "EMFILE"
    go EMLINK = "EMLINK"
    go EMSGSIZE = "EMSGSIZE"
    go EMULTIHOP = "EMULTIHOP"
    go ENAMETOOLONG = "ENAMETOOLONG"
    go ENETDOWN = "ENETDOWN"
    go ENETRESET = "ENETRESET"
    go ENETUNREACH = "ENETUNREACH"
    go ENFILE = "ENFILE"
    go ENOBUFS = "ENOBUFS"
    go ENODATA = "ENODATA"
    go ENODEV = "ENODEV"
    go ENOENT = "ENOENT"
    go ENOEXEC = "ENOEXEC"
    go ENOLCK = "ENOLCK"
    go ENOLINK = "ENOLINK"
    go ENOMEM = "ENOMEM"
    go ENONET = "ENONET"
    go ENOPROTOOPT = "ENOPROTOOPT"
    go ENOSPC = "ENOSPC"
    go ENOSR = "ENOSR"
    go ENOSTR = "ENOSTR"
    go ENOSYS = "ENOSYS"
    go ENOTBLK = "ENOTBLK"
    go ENOTCONN = "ENOTCONN"
    go ENOTDIR = "ENOTDIR"
    go ENOTEMPTY = "ENOTEMPTY"
    go ENOTSOCK = "ENOTSOCK"
    go ENOTSUP = "ENOTSUP"
    go EPERM = "EPERM"
    go EPFNOSUPPORT = "EPFNOSUPPORT"
    go EPIPE = "EPIPE"
    go EPROCLIM = "EPROCLIM"
    go EPROCUNAVAIL = "EPROCUNAVAIL"
    go EPROGMISMATCH = "EPROGMISMATCH"
    go EPROGUNAVAIL = "EPROGUNAVAIL"
    go EPROTO = "EPROTO"
    go EPROTONOSUPPORT = "EPROTONOSUPPORT"
    go EPROTOTYPE = "EPROTOTYPE"
    go ERANGE = "ERANGE"
    go EREMCHG = "EREMCHG"
    go EREMOTE = "EREMOTE"
    go ESHUTDOWN = "ESHUTDOWN"
    go ESOCKTNOSUPPORT = "ESOCKTNOSUPPORT"
    go ESPIPE = "ESPIPE"
    go ESRCH = "ESRCH"
    go ESRMNT = "ESRMNT"
    go ESTALE = "ESTALE"
    go ETIME = "ETIME"
    go ETIMEDOUT = "ETIMEDOUT"
    go ETOOMANYREFS = "ETOOMANYREFS"
    go ETXTBSY = "ETXTBSY"
    go EUSERS = "EUSERS"
    go EWOULDBLOCK = "EWOULDBLOCK"
    go EXDEV = "EXDEV"
    go (Errno i) = "(Errno " P.++ P.show i P.++ ")"

-- ** Common @errno@ symbols
pattern EOK             = Errno 0
pattern E2BIG           = Errno (CONST_E2BIG)
pattern EACCES          = Errno (CONST_EACCES)
pattern EADDRINUSE      = Errno (CONST_EADDRINUSE)
pattern EADDRNOTAVAIL   = Errno (CONST_EADDRNOTAVAIL)
pattern EADV            = Errno (CONST_EADV)
pattern EAFNOSUPPORT    = Errno (CONST_EAFNOSUPPORT)
pattern EAGAIN          = Errno (CONST_EAGAIN)
pattern EALREADY        = Errno (CONST_EALREADY)
pattern EBADF           = Errno (CONST_EBADF)
pattern EBADMSG         = Errno (CONST_EBADMSG)
pattern EBADRPC         = Errno (CONST_EBADRPC)
pattern EBUSY           = Errno (CONST_EBUSY)
pattern ECHILD          = Errno (CONST_ECHILD)
pattern ECOMM           = Errno (CONST_ECOMM)
pattern ECONNABORTED    = Errno (CONST_ECONNABORTED)
pattern ECONNREFUSED    = Errno (CONST_ECONNREFUSED)
pattern ECONNRESET      = Errno (CONST_ECONNRESET)
pattern EDEADLK         = Errno (CONST_EDEADLK)
pattern EDESTADDRREQ    = Errno (CONST_EDESTADDRREQ)
pattern EDIRTY          = Errno (CONST_EDIRTY)
pattern EDOM            = Errno (CONST_EDOM)
pattern EDQUOT          = Errno (CONST_EDQUOT)
pattern EEXIST          = Errno (CONST_EEXIST)
pattern EFAULT          = Errno (CONST_EFAULT)
pattern EFBIG           = Errno (CONST_EFBIG)
pattern EFTYPE          = Errno (CONST_EFTYPE)
pattern EHOSTDOWN       = Errno (CONST_EHOSTDOWN)
pattern EHOSTUNREACH    = Errno (CONST_EHOSTUNREACH)
pattern EIDRM           = Errno (CONST_EIDRM)
pattern EILSEQ          = Errno (CONST_EILSEQ)
pattern EINPROGRESS     = Errno (CONST_EINPROGRESS)
pattern EINTR           = Errno (CONST_EINTR)
pattern EINVAL          = Errno (CONST_EINVAL)
pattern EIO             = Errno (CONST_EIO)
pattern EISCONN         = Errno (CONST_EISCONN)
pattern EISDIR          = Errno (CONST_EISDIR)
pattern ELOOP           = Errno (CONST_ELOOP)
pattern EMFILE          = Errno (CONST_EMFILE)
pattern EMLINK          = Errno (CONST_EMLINK)
pattern EMSGSIZE        = Errno (CONST_EMSGSIZE)
pattern EMULTIHOP       = Errno (CONST_EMULTIHOP)
pattern ENAMETOOLONG    = Errno (CONST_ENAMETOOLONG)
pattern ENETDOWN        = Errno (CONST_ENETDOWN)
pattern ENETRESET       = Errno (CONST_ENETRESET)
pattern ENETUNREACH     = Errno (CONST_ENETUNREACH)
pattern ENFILE          = Errno (CONST_ENFILE)
pattern ENOBUFS         = Errno (CONST_ENOBUFS)
pattern ENODATA         = Errno (CONST_ENODATA)
pattern ENODEV          = Errno (CONST_ENODEV)
pattern ENOENT          = Errno (CONST_ENOENT)
pattern ENOEXEC         = Errno (CONST_ENOEXEC)
pattern ENOLCK          = Errno (CONST_ENOLCK)
pattern ENOLINK         = Errno (CONST_ENOLINK)
pattern ENOMEM          = Errno (CONST_ENOMEM)
pattern ENOMSG          = Errno (CONST_ENOMSG)
pattern ENONET          = Errno (CONST_ENONET)
pattern ENOPROTOOPT     = Errno (CONST_ENOPROTOOPT)
pattern ENOSPC          = Errno (CONST_ENOSPC)
pattern ENOSR           = Errno (CONST_ENOSR)
pattern ENOSTR          = Errno (CONST_ENOSTR)
pattern ENOSYS          = Errno (CONST_ENOSYS)
pattern ENOTBLK         = Errno (CONST_ENOTBLK)
pattern ENOTCONN        = Errno (CONST_ENOTCONN)
pattern ENOTDIR         = Errno (CONST_ENOTDIR)
pattern ENOTEMPTY       = Errno (CONST_ENOTEMPTY)
pattern ENOTSOCK        = Errno (CONST_ENOTSOCK)
pattern ENOTSUP         = Errno (CONST_ENOTSUP)
pattern ENOTTY          = Errno (CONST_ENOTTY)
pattern ENXIO           = Errno (CONST_ENXIO)
pattern EOPNOTSUPP      = Errno (CONST_EOPNOTSUPP)
pattern EPERM           = Errno (CONST_EPERM)
pattern EPFNOSUPPORT    = Errno (CONST_EPFNOSUPPORT)
pattern EPIPE           = Errno (CONST_EPIPE)
pattern EPROCLIM        = Errno (CONST_EPROCLIM)
pattern EPROCUNAVAIL    = Errno (CONST_EPROCUNAVAIL)
pattern EPROGMISMATCH   = Errno (CONST_EPROGMISMATCH)
pattern EPROGUNAVAIL    = Errno (CONST_EPROGUNAVAIL)
pattern EPROTO          = Errno (CONST_EPROTO)
pattern EPROTONOSUPPORT = Errno (CONST_EPROTONOSUPPORT)
pattern EPROTOTYPE      = Errno (CONST_EPROTOTYPE)
pattern ERANGE          = Errno (CONST_ERANGE)
pattern EREMCHG         = Errno (CONST_EREMCHG)
pattern EREMOTE         = Errno (CONST_EREMOTE)
pattern EROFS           = Errno (CONST_EROFS)
pattern ERPCMISMATCH    = Errno (CONST_ERPCMISMATCH)
pattern ERREMOTE        = Errno (CONST_ERREMOTE)
pattern ESHUTDOWN       = Errno (CONST_ESHUTDOWN)
pattern ESOCKTNOSUPPORT = Errno (CONST_ESOCKTNOSUPPORT)
pattern ESPIPE          = Errno (CONST_ESPIPE)
pattern ESRCH           = Errno (CONST_ESRCH)
pattern ESRMNT          = Errno (CONST_ESRMNT)
pattern ESTALE          = Errno (CONST_ESTALE)
pattern ETIME           = Errno (CONST_ETIME)
pattern ETIMEDOUT       = Errno (CONST_ETIMEDOUT)
pattern ETOOMANYREFS    = Errno (CONST_ETOOMANYREFS)
pattern ETXTBSY         = Errno (CONST_ETXTBSY)
pattern EUSERS          = Errno (CONST_EUSERS)
pattern EWOULDBLOCK     = Errno (CONST_EWOULDBLOCK)
pattern EXDEV           = Errno (CONST_EXDEV)

-- ** 'Errno' functions

-- | Yield 'True' if the given 'Errno' value is valid on the system.
-- This implies that the 'Eq' instance of 'Errno' is also system dependent
-- as it is only defined for valid values of 'Errno'.
--
isValidErrno               :: Errno -> Bool
-- the configure script sets all invalid "errno"s to -1
isValidErrno (Errno errno)  = errno P./= -1

-- | Get the current value of @errno@ in the current thread.
-- We must call a C function to get the value of errno in general.  On
-- threaded systems, errno is hidden behind a C macro so that each OS
-- thread gets its own copy.
foreign import ccall unsafe "HsBase.h __hscore_get_errno" getErrno :: IO Errno

-- | Reset the current thread's errno value to 'OK'
resetErrno = setErrno EOK 
-- | Set the current thread's errno value
foreign import ccall unsafe "HsBase.h __hscore_set_errno" setErrno :: Errno -> IO ()

foreign import ccall unsafe "string.h" strerror :: Errno -> IO (P.Ptr U8)
describeErrno e = P.unsafePerformIO (strerror e P.>>= \x -> P.peekCString (P.castPtr x))
displayErrno e = P.show e P.++ "( " P.++ describeErrno e P.++ ")"
  
  

errnoToIOError loc errno maybeHdl maybeName = P.unsafePerformIO do
    str <- strerror errno P.>>= \x -> P.peekCString (P.castPtr x)
    P.return (P.IOError maybeHdl errType loc str (P.Just $ coerce errno) maybeName)
    where
      errType = case errno of
        EOK             -> P.OtherError
        E2BIG           -> P.ResourceExhausted
        EACCES          -> P.PermissionDenied
        EADDRINUSE      -> P.ResourceBusy
        EADDRNOTAVAIL   -> P.UnsupportedOperation
        EADV            -> P.OtherError
        EAFNOSUPPORT    -> P.UnsupportedOperation
        EAGAIN          -> P.ResourceExhausted
        EALREADY        -> P.AlreadyExists
        EBADF           -> P.InvalidArgument
        EBADMSG         -> P.InappropriateType
        EBADRPC         -> P.OtherError
        EBUSY           -> P.ResourceBusy
        ECHILD          -> P.NoSuchThing
        ECOMM           -> P.ResourceVanished
        ECONNABORTED    -> P.OtherError
        ECONNREFUSED    -> P.NoSuchThing
        ECONNRESET      -> P.ResourceVanished
        EDEADLK         -> P.ResourceBusy
        EDESTADDRREQ    -> P.InvalidArgument
        EDIRTY          -> P.UnsatisfiedConstraints
        EDOM            -> P.InvalidArgument
        EDQUOT          -> P.PermissionDenied
        EEXIST          -> P.AlreadyExists
        EFAULT          -> P.OtherError
        EFBIG           -> P.PermissionDenied
        EFTYPE          -> P.InappropriateType
        EHOSTDOWN       -> P.NoSuchThing
        EHOSTUNREACH    -> P.NoSuchThing
        EIDRM           -> P.ResourceVanished
        EILSEQ          -> P.InvalidArgument
        EINPROGRESS     -> P.AlreadyExists
        EINTR           -> P.Interrupted
        EINVAL          -> P.InvalidArgument
        EIO             -> P.HardwareFault
        EISCONN         -> P.AlreadyExists
        EISDIR          -> P.InappropriateType
        ELOOP           -> P.InvalidArgument
        EMFILE          -> P.ResourceExhausted
        EMLINK          -> P.ResourceExhausted
        EMSGSIZE        -> P.ResourceExhausted
        EMULTIHOP       -> P.UnsupportedOperation
        ENAMETOOLONG    -> P.InvalidArgument
        ENETDOWN        -> P.ResourceVanished
        ENETRESET       -> P.ResourceVanished
        ENETUNREACH     -> P.NoSuchThing
        ENFILE          -> P.ResourceExhausted
        ENOBUFS         -> P.ResourceExhausted
        ENODATA         -> P.NoSuchThing
        ENODEV          -> P.UnsupportedOperation
        ENOENT          -> P.NoSuchThing
        ENOEXEC         -> P.InvalidArgument
        ENOLCK          -> P.ResourceExhausted
        ENOLINK         -> P.ResourceVanished
        ENOMEM          -> P.ResourceExhausted
        ENOMSG          -> P.NoSuchThing
        ENONET          -> P.NoSuchThing
        ENOPROTOOPT     -> P.UnsupportedOperation
        ENOSPC          -> P.ResourceExhausted
        ENOSR           -> P.ResourceExhausted
        ENOSTR          -> P.InvalidArgument
        ENOSYS          -> P.UnsupportedOperation
        ENOTBLK         -> P.InvalidArgument
        ENOTCONN        -> P.InvalidArgument
        ENOTDIR         -> P.InappropriateType
        ENOTEMPTY       -> P.UnsatisfiedConstraints
        ENOTSOCK        -> P.InvalidArgument
        ENOTTY          -> P.IllegalOperation
        ENXIO           -> P.NoSuchThing
        EOPNOTSUPP      -> P.UnsupportedOperation
        EPERM           -> P.PermissionDenied
        EPFNOSUPPORT    -> P.UnsupportedOperation
        EPIPE           -> P.ResourceVanished
        EPROCLIM        -> P.PermissionDenied
        EPROCUNAVAIL    -> P.UnsupportedOperation
        EPROGMISMATCH   -> P.ProtocolError
        EPROGUNAVAIL    -> P.UnsupportedOperation
        EPROTO          -> P.ProtocolError
        EPROTONOSUPPORT -> P.ProtocolError
        EPROTOTYPE      -> P.ProtocolError
        ERANGE          -> P.UnsupportedOperation
        EREMCHG         -> P.ResourceVanished
        EREMOTE         -> P.IllegalOperation
        EROFS           -> P.PermissionDenied
        ERPCMISMATCH    -> P.ProtocolError
        ERREMOTE        -> P.IllegalOperation
        ESHUTDOWN       -> P.IllegalOperation
        ESOCKTNOSUPPORT -> P.UnsupportedOperation
        ESPIPE          -> P.UnsupportedOperation
        ESRCH           -> P.NoSuchThing
        ESRMNT          -> P.UnsatisfiedConstraints
        ESTALE          -> P.ResourceVanished
        ETIME           -> P.TimeExpired
        ETIMEDOUT       -> P.TimeExpired
        ETOOMANYREFS    -> P.ResourceExhausted
        ETXTBSY         -> P.ResourceBusy
        EUSERS          -> P.ResourceExhausted
        EWOULDBLOCK     -> P.OtherError
        EXDEV           -> P.UnsupportedOperation
        _               -> P.OtherError


-- ** Guards for IO operations that may fail

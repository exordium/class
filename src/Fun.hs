{-# language FlexibleContexts #-}
{-# language MagicHash #-}
{-# language UndecidableSuperClasses #-}
{-# language DefaultSignatures #-}
{-# language FunctionalDependencies #-}
module Fun (module Fun, module X) where
{-import Promap-}
import GHC.Types as X (Bool(..),IO,Char)
import GHC.Prim as X (TYPE)
import GHC.Base as X (id)
import GHC.Stack as X (HasCallStack)
import qualified GHC.Prim as GHC
import qualified GHC.Base as GHC
import qualified Unsafe.Coerce as GHC
import qualified Data.Coerce as GHC
import Fun.Named as X

import Church

fix :: (a -> a) -> a
fix f = f (fix f)

{-# INLINE (>) #-}
(>) :: (a -> x) -> (x -> b) -> a -> b
f > g = \a -> g (f a)

infixr 9 <
{-# INLINE (<) #-}
(<) :: (x -> b) -> (a -> x) -> a -> b
(<) = (GHC..)

infixr 9 <<
{-# inline (<<) #-}
(<<) :: (x -> c) -> (a -> b -> x) -> a -> b -> c
f << g = \a b -> f (g a b)

infixl ?
{-# INLINE (?) #-}
(?) :: forall a r. Church a => a -> ChurchRep a r
(?) = churchEncode @a @r

{-# inline ($:) #-}
f $: (a,b) = f a b
{-# inline (.$) #-}
(.$) :: (a -> b -> c) -> b -> a -> c
(f .$ b) a = f a b

-- | Application operator.  This operator is redundant, since ordinary
-- application @(f x)@ means the same as @(f '$' x)@. However, '$' has
-- low, binding precedence, so it sometimes allows
-- parentheses to be omitted; for example:
--
-- > f < g < h $ x
-- >   $ modifying % some > long > expression
-- >   $ y
-- > = f (g (h x)) (expression (long (some modifying))) y
--
--
--
-- It is also useful in higher-order situations, such as @'map' ('$' 0) xs@,
-- or @'zipWith' ('$') fs xs@.
infixl 1 $, $!
{-# inline ($) #-}; {-# inline ($!) #-}
($),($!):: forall r a (b :: TYPE r). (a -> b) -> a -> b
($) = (GHC.$)
-- | Strict (call-by-value) application operator. It takes a function and an
-- argument, evaluates the argument to weak head normal form (WHNF), then calls
-- the function with that value.
($!) = (GHC.$!)


{-# inline (!) #-}
(!) :: a -> b -> a
(!) = GHC.const
{-# inline (!!) #-}
(!!) :: a -> b -> a
a !! b = GHC.seq b a

infixl 2 %, !%
{-# inline (%) #-}; {-# inline (!%) #-}
(%), (!%) :: a -> (a -> b) -> b
a % f = f a
(!%) !a f = f a


-- | A special case of 'error'.
-- It is expected that compilers will recognize this and insert error
-- messages which are more appropriate to the context in which 'undefined'
-- appears. Useful for debugging and when you know it won't be evaluated.
_# :: HasCallStack => a
_# = GHC.undefined

-- | The function @coerce#\#@ allows you to side-step the typechecker entirely. That
--         is, it allows you to coerce any type into any other type. If you use this function,
--         you had better get it right, otherwise segmentation faults await. It is generally
--         used when you want to write a program that you know is well-typed, but where Haskell\'s
--         type system is not expressive enough to prove that it is well typed.
-- 
--         The following uses of @coerce#\#@ are supposed to work (i.e. not lead to
--         spurious compile-time or run-time crashes):
-- 
--          * Casting any lifted type to @Any@
-- 
--          * Casting @Any@ back to the real type
-- 
--          * Casting an unboxed type to another unboxed type of the same size.
--            (Casting between floating-point and integral types does not work.
--            See the @GHC.Float@ module for functions to do work.)
-- 
--          * Casting between two types that have the same runtime representation.  One case is when
--            the two types differ only in \"phantom\" type parameters, for example
--            @Ptr Int@ to @Ptr Float@, or @[Int]@ to @[Float]@ when the list is
--            known to be empty.  Also, a @newtype@ of a type @T@ has the same representation
--            at runtime as @T@.
-- 
--         Other uses of @coerce#\#@ are undefined.  In particular, you should not use
--         @coerce#\#@ to cast a T to an algebraic data type D, unless T is also
--         an algebraic data type.  For example, do not cast @Int->Int@ to @Bool@, even if
--         you later cast that @Bool@ back to @Int->Int@ before applying it.  The reasons
--         have to do with GHC\'s internal representation details (for the cognoscenti, data values
--         can be entered but function closures cannot).  If you want a safe type to cast things
--         to, use @Any@, which is not an algebraic data type.
{-# inline coerce# #-}
coerce# :: a -> b
coerce# = GHC.unsafeCoerce

type (=#) = GHC.Coercible
-- | The function @coerce@ allows you to safely convert between values of
-- types that have the same representation with no run-time overhead. In the
-- simplest case you can use it instead of a newtype constructor, to go from
-- the newtype\'s concrete type to the abstract type. But it also works in
-- more complicated settings, e.g. converting a list of newtypes to a list of
-- concrete types.
-- Useful with @-XTypeApplications@. eg:
--
-- > coerce @Int :: Int =# a => a -> Int
{-# inline coerce #-}
coerce :: b =# a => a -> b
coerce = GHC.coerce

-- | Representational Equality on functors
class    (forall a. f a =# g a) => f #=# g
instance (forall a. f a =# g a) => f #=# g
coerce1 :: forall g f a. f #=# g => f a -> g a
coerce1 = GHC.coerce

f $# a = f (coerce a)

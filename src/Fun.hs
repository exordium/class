{-# language FlexibleContexts #-}
{-# language MagicHash #-}
{-# language UndecidableSuperClasses #-}
{-# language DefaultSignatures #-}
{-# language FunctionalDependencies #-}
module Fun (module Fun, module X) where
{-import Promap-}
import qualified Prelude as P
import Prelude as X (Bool(..),IO,print,Char,Double,Int,Maybe(..),maybe,Integer,Integral(..),Num(..))
import Data.Maybe (fromMaybe)
import Named as X (WithParam,(:!),(:?),arg)
import Named.Internal as X (Param(..),Decide)
import qualified Named
import qualified Named.Internal as Named
import Church
import Type.E
import GHC.Prim
import qualified Unsafe.Coerce as GHC
import qualified Data.Coerce as GHC


(>) :: (a -> x) -> (x -> b) -> a -> b
f > g = \a -> g (f a); {-# INLINE (>) #-}

(<) :: (x -> b) -> (a -> x) -> a -> b
f < g = \a -> f (g a); {-# INLINE (<) #-}
infixr <

(?) :: forall a r. Church a => a -> ChurchRep a r
-- | 
(?) = churchEncode @a @r; {-# INLINE (?) #-}
infixl ?

pattern Arg' :: Maybe a -> Named.NamedF Maybe a name
pattern Arg' b = Named.ArgF b

arg' :: Named.Name name -> Named.NamedF Maybe a name -> Maybe a
arg' = Named.argF

{-(^) :: -}
f $ a = f a
($!) f !a = f a
infixl 1 $, $!, $$, $., &

(!) :: a -> b -> a
(!) = P.const; {-# inline (!) #-}
(!!) = seq; {-# INLINE (!!) #-}

a & f = f a
(!&) !a f = f a

-- | 
-- prop> downcast < upcast = id
class super ~>~ sub where
  upcast :: sub -> super
  downcast :: super -> sub
instance a ~>~ a where {upcast a = a; downcast a = a}
instance Integer ~>~ Int where {upcast = toInteger; downcast = fromInteger}
{-instance Integral a => Int ~>~ Integer where {upcast = toInteger; downcast = Just < fromInteger}-}

-- | 'downcast' an argument before feeding it to a function. Useful for literal overloading in the absence of 'Num' magic
(%) :: forall super sub r. super ~>~ sub => (sub -> r) -> super -> r
(%) = (<downcast)
{-# INLINE (%) #-}



-- | Supply a named parameter to a function:
-- 
-- > foob a b (arg #x -> x) = ...
-- > foob
-- >    ! a + b
-- >    ! reverse "Hello"
-- >    !! #x(7)
-- >    !! #y(42)
-- >    !! defaults

($$) :: WithParam p fn fn' => fn -> Param p -> fn'
($$) = (Named.!)

-- | Pass a named argument positionally
($.) :: Named.InjValue f => (Named.NamedF f a name -> b) -> a -> b
($.) f = f < Named.ArgF < Named.injValue
{-(!.) f a = f (Named.ArgF (Named.injValue a))-}

{-foo :: Int -> "bar" :! Int -> "foo" :? Char -> IO ()-}
foo i (arg #bar -> b) (arg' #foo -> f) = do
  print i
  print b
  print $ fromMaybe "" f

ff = (P.* (2::Int)) %(10::Integer)  

__ = P.undefined

{-(|||) :: (a -> r) -> (b -> r) -> E a b -> r-}
{-f ||| g = \case {L a -> f a; R b -> g b}-}
{-(+++) :: (x -> a) -> (y -> b) -> E x y -> E a b-}
{-f +++ g = (L < f) ||| (R < g)-}

{-(&&&) :: (x -> a) -> (x -> b) -> x -> (a,b)-}
{-f &&& g = \x -> (f x, g x)-}
{-(***) :: (x -> a) -> (y -> b) -> (x,y) -> (a,b)-}
{-f *** g = \(x,y) -> (f x, g y)-}

id :: a -> a
id a = a

coerce# :: a -> b
coerce# = GHC.unsafeCoerce

type (=#) = GHC.Coercible
coerce :: b =# a => a -> b
coerce = GHC.coerce; {-# INLINE coerce #-}
(#) :: forall a b. (a =# b) => (a -> b) -> a -> b
(#) _ = GHC.coerce @a @b

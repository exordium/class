{-# language FlexibleContexts #-}
{-# language UndecidableSuperClasses #-}
{-# language DefaultSignatures #-}
{-# language FunctionalDependencies #-}
module Fun (module Fun, module X) where
import Promap
import qualified Prelude as P
import Prelude as X (($),($!))
import Prelude as X (Bool(..),IO,print,Char,Double,Int,(+),Maybe(..),maybe,Integer,Integral(..),Num(..))
import Data.Maybe (fromMaybe)
import Named as X (WithParam,(:!),(:?))
import Named.Internal as X (Param(..),Decide)
import qualified Named
import qualified Named.Internal as Named
import Church


data Foob a b = Foob a b | Foo a | B b
(>) :: (a -> x) -> (x -> b) -> a -> b
f > g = \a -> g (f a); {-# INLINE (>) #-}
infixl >

(<) :: (x -> b) -> (a -> x) -> a -> b
f < g = \a -> f (g a); {-# INLINE (<) #-}
infixr <

(?) :: forall a r. Church a => a -> ChurchRep a r
-- | 
(?) = churchEncode @a @r; {-# INLINE (?) #-}
infixl ?

{-class Def a b where (?) :: a -> b -> b-}

instance Fun' (Maybe a) a a 
instance Fun (Maybe a) a a where
  (!)= \case { Nothing -> \x -> x; Just a -> \_ -> a}
  
{-instance Def (Maybe a)  where-}
  {-(?) = \case { Nothing -> \x -> x; Just a -> \_ -> a}-}
{-instance Def Bool a where-}
{-instance Fun Bool a (a -> a) where-}
  {-(!)  b f = case b of-}
      {-False -> \_ -> f-}
      {-True -> \x -> x-}
{-class Def a where def :: a-}
{-instance Def (Named.Param Named.Defaults) where def = Named.defaults-}

pattern Arg' :: Maybe a -> Named.NamedF Maybe a name
pattern Arg' b = Named.ArgF b

arg' :: Named.Name name -> Named.NamedF Maybe a name -> Maybe a
arg' = Named.argF

{-(^) :: -}
class Fun' p a b | p -> a b where
  (!?) :: p -> a -> Maybe b
  default (!?) :: Fun p a b => p -> a -> Maybe b
  f !? a = Just (f ! a)
class Fun' p a b => Fun p a b | p -> a b where (!) :: p -> a -> b
instance Fun' (a -> b) a b
instance Fun (a -> b) a b where (!) f a = f a
infixl 1 !, !?, !!, !.

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

(!!) :: WithParam p fn fn' => fn -> Param p -> fn'
(!!) = (Named.!)

-- | Pass a named argument positionally
(!.) :: Named.InjValue f => (Named.NamedF f a name -> b) -> a -> b
(!.) f = f < Named.ArgF < Named.injValue
{-(!.) f a = f (Named.ArgF (Named.injValue a))-}

{-foo :: Int -> "bar" :! Int -> "foo" :? Char -> IO ()-}
foo i (arg #bar -> b) (arg' #foo -> f) = do
  print i
  print b
  print $ fromMaybe "" f

f = foo
  !3
  {-{-!! #bar(10)-}-}
  !! #foo("wow")
  !. 10

{-f %3-}
  {-%5-}
  {-%"wowo"-}

{-f ^(3 + 3)-}
  {-^(5 - 10)-}
  {-^("wowo" ++ "a")-}

{-f !.(3 + 3)-}
  {-!. #length 3-}
  {-!.("wowo" ++ "a")-}

{-f .3-}
  {-.5-}
  {-."wowo"-}

{-f &3-}
  {-&5-}
  {-&"wowo"-}

{-f !3-}
  {-!5-}
  {-!"wowo"-}


{-f ?3-}
  {-?5-}
  {-?"wowo"-}

{-(!) 3-}

{-(?) 2 -}

ff = (P.* (2::Int)) %(10::Integer)  

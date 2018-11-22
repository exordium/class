{-# language TemplateHaskell #-}
module Map where
{-import Traverse-}
{-class (Traverse ((~) I) f, Strong f) => Map f where-}

{-class (Strong f) => Map f where-}
  {-map :: (a -> b) -> f a -> f b-}
  {-constMap :: b -> f a -> f b-}
  {-constMap b = map \ _ -> b-}

{-instance Impl Map where-}
  {-type Methods Map = '["map"]-}
  {-impl f (Arg map) = [d|-}
    {-instance Map    $f where map      = $map-}
    {-instance Strong $f where strong a = $map ((,) a)-}
    {-instance Remap  $f where remap _  = $map-}
   {-|]-}

{-instance Map ((->) x) where map f g = \a ->  f (g a)-}
{-instance Map [] where map = P.map-}
{-instance Map (E x) where map f = \case {L x -> L x; R a -> R (f a)}-}
{-instance Map I where map f (I a) = I (f a)-}
{-instance Map ((,) x) where map f (x,a) = (x, f a)-}
{-instance Map P.IO where map = P.fmap-}

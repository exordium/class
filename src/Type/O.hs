module Type.O where

newtype O (f :: * -> *) (g :: * -> *) a = O {unO :: f (g a)}

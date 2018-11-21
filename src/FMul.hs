module FMul where
import Remap

class Remap f => FMul f where fmul :: f a -> f b -> f (a,b)

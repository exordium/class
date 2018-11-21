module IsEither where
import Map
import E

type family LeftF t where LeftF (E a) = a
class (Map f, f ~ E (LeftF f)) => IsEither f
instance IsEither (E a)

type family Left t where Left (E a b) = a
type family Right t where Right (E a b) = b
class a ~ E (Left a) (Right a) => IsEither' a
instance a ~ E (Left a) (Right a) => IsEither' a

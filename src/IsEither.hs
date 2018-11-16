module IsEither where
import Map
import E

type family Left t where Left (E a) = a
class (Map f, f ~ E (Left f)) => IsEither f
instance IsEither (E a)

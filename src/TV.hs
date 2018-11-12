{-# OPTIONS_GHC -Wno-missing-fields #-}
module TV where
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote

-- | 'QuasiQuoter' for a capturable type variable. Ex:
--
--  >>> runQ [t|Applicative [tv|m|] => Monad [tv|m|]|]
--  ForallT [] [AppT (ConT GHC.Base.Monad) (VarT m)] (AppT (ConT GHC.Base.Applicative) (VarT m))

tv = QuasiQuoter {quoteType = \s -> returnQ (VarT (mkName s))}


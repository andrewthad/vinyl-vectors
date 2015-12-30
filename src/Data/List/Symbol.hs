module Data.List.Symbol where

import Data.List.TypeLevel (IfOrd)
import GHC.TypeLits

type family Union (a :: [Symbol]) (b :: [Symbol]) :: [Symbol] where
  Union '[] '[] = '[]
  Union '[] (b ': bs) = b ': Union '[] bs 
  Union (a ': as) '[] = a ': Union as '[]
  Union (a ': as) (b ': bs) = 
    IfOrd (CmpSymbol a b)
      (b ': Union (a ': as) bs)
      (a ': Union as bs)
      (a ': Union as (b ': bs))



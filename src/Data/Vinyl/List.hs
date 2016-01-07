module Data.Vinyl.List where

import Data.Vinyl.Core
import Data.Vinyl.Functor (Identity(..))
import Data.List.TypeLevel (AllAre)

-- listToHomogeneousRec :: AllAre a as => [a] -> Rec Identity as
-- listToHomogeneousRec [] = RNil
-- listToHomogeneousRec (a : as) = Identity a :& listToHomogeneousRec as


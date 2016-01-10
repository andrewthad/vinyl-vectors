module Data.Vinyl.DictFun where

import           Data.Constraint
import           Data.List.TypeLevel.Constraint (ListAll)
import           Data.Proxy
import           Data.Vinyl.Core                hiding (Dict)
import           GHC.Exts                       (Constraint)

data DictFun (c :: k -> Constraint) (a :: k) where
  DictFun :: c a => DictFun c a

dictFunOf :: Proxy c -> Dict (c a) -> DictFun c a
dictFunOf _ Dict = DictFun

reifyDictFun :: ListAll rs c => proxy1 c -> Rec proxy2 rs -> Rec (DictFun c) rs
reifyDictFun _ RNil = RNil
reifyDictFun p (_ :& rs) = DictFun :& reifyDictFun p rs


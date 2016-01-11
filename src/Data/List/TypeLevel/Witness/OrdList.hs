module Data.List.TypeLevel.Witness.OrdList where

import           Prelude                     hiding (head, tail)

import           Data.List.TypeLevel.Witness
import           Data.Proxy

tail :: OrdList (c ': cs) -> OrdList cs
tail OrdListSingle = OrdListNil
tail (OrdListCons x) = x

head :: OrdList (c ': cs) -> Proxy c
head OrdListSingle = Proxy
head (OrdListCons _) = Proxy

toBoundedList :: OrdList (a ': as) -> BoundedList a as
toBoundedList o = case o of
  OrdListSingle -> BoundedListNil
  OrdListCons _ -> BoundedListCons


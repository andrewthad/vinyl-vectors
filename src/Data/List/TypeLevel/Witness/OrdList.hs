module Data.List.TypeLevel.Witness.OrdList where

import           Prelude                     hiding (head, tail)

import           Data.Constraint
import           Data.List.TypeLevel.Cmp
import           Data.List.TypeLevel.Witness
import           Data.Proxy
import           Data.Tuple.TypeLevel

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

sublist :: Sublist super sub -> OrdList super -> OrdList sub
sublist = go
  where
  go :: Sublist super sub -> OrdList super -> OrdList sub
  go SublistNil OrdListNil = OrdListNil
  go (SublistBoth SublistNil) OrdListSingle = OrdListSingle
  go (SublistSuper SublistNil) OrdListSingle = OrdListNil
  go (SublistSuper snext) (OrdListCons onext) = go snext onext
  go (SublistBoth snext) ol@(OrdListCons onext) = case lemma1 snext ol of
    BoundedListCons -> OrdListCons (go snext onext)
    BoundedListNil  -> OrdListSingle
  -- case go snext onext of
  --   OrdListNil -> OrdListSingle
  --   OrdListSingle -> OrdListCons OrdListSingle

lemma1 :: Sublist super sub -> OrdList (b ': super) -> BoundedList b sub
lemma1 (SublistBoth s') (OrdListCons o') = BoundedListCons
lemma1 (SublistSuper s') o@(OrdListCons o'@(OrdListCons o'')) =
  case transitiveLT (proxyFst $ head o'') (proxyFst $ head o') (proxyFst $ head o) of
    Sub Dict -> lemma1 s' (OrdListCons o'')


{-# LANGUAGE PartialTypeSignatures #-}

module Data.List.TypeLevel.Union where

import           Data.List.TypeLevel.Cmp
import           Data.List.TypeLevel.Constraint ((:&:))
import           Data.Tuple.TypeLevel
import           Data.Type.Equality
import           Data.Typeable
import           Data.TypeString
import           Data.Vinyl.Core                hiding (Dict)
import           Data.Vinyl.DictFun

-- This is NOT total.
type family Union (a :: [(k,v)]) (b :: [(k,v)]) :: [(k,v)] where
  Union '[] '[] = '[]
  Union '[] (b ': bs) = b ': Union '[] bs
  Union (a ': as) '[] = a ': Union as '[]
  Union (a ': as) (b ': bs) = UnionCmp (Cmp (Fst a) (Fst b)) a as b bs

type family UnionCmp (o :: Ordering) (a :: (k,v)) (as :: [(k,v)]) (b :: (k,v)) (bs :: [(k,v)]) where
  UnionCmp 'LT a as b bs = b ': Union (a ': as) bs
  UnionCmp 'EQ a as b bs = a ': Union as bs
  UnionCmp 'GT a as b bs = a ': Union as (b ': bs)

commutativity :: forall (as :: [(k,*)]) (bs :: [(k,*)]).
     Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)) as
  -> Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)) bs
  -> Union as bs :~: Union bs as
commutativity = go
  where
  go :: forall (as1 :: [(k,*)]) (bs1 :: [(k,*)]).
       Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)) as1
    -> Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)) bs1
    -> Union as1 bs1 :~: Union bs1 as1
  go RNil RNil = Refl
  go ((DictFun :: _ a) :& asNext) ((DictFun :: _ b) :& bsNext) = case go asNext bsNext of
    Refl -> case compareTypes (Proxy :: Proxy (Fst a)) (Proxy :: Proxy (Fst b)) of
      CmpEQ -> Refl


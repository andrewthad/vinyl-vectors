{-# LANGUAGE PartialTypeSignatures #-}

module Data.List.TypeLevel.Union where

import           Data.Constraint
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

leftIdentity :: Rec proxy xs -> Union '[] xs :~: xs
leftIdentity RNil = Refl
leftIdentity (_ :& rs) = case leftIdentity rs of
  Refl -> Refl

rightIdentity :: Rec proxy xs -> Union xs '[] :~: xs
rightIdentity RNil = Refl
rightIdentity (_ :& rs) = case rightIdentity rs of
  Refl -> Refl

associativity :: Rec CmpDict as -> Rec CmpDict bs -> Rec CmpDict cs
              -> Union (Union as bs) cs :~: Union as (Union bs cs)
associativity = go
  where
  go :: forall as bs cs. Rec CmpDict as -> Rec CmpDict bs -> Rec CmpDict cs
     -> Union (Union as bs) cs :~: Union as (Union bs cs)
  go RNil RNil RNil = Refl
  go as RNil cs = case rightIdentity as of
    Refl -> case leftIdentity cs of
      Refl -> Refl
  go as bs RNil = case rightIdentity bs of
    Refl -> case rightIdentity (rec as bs) of
      Refl -> Refl
  go RNil bs cs = case leftIdentity bs of
    Refl -> case leftIdentity (rec bs cs) of
      Refl -> Refl
  go (a@DictFun :& anext) (b@DictFun :& bnext) (c@DictFun :& cnext) =
    case compareTypes (proxyFst a) (proxyFst b) of
      CmpEQ -> case compareTypes (proxyFst b) (proxyFst c) of
        CmpEQ -> case go anext bnext cnext of
          Refl -> Refl
        CmpLT -> case go (a :& anext) (b :& bnext) cnext of
          Refl -> Refl
        CmpGT -> case go anext bnext (c :& cnext) of
          Refl -> Refl
      CmpGT -> case compareTypes (proxyFst b) (proxyFst c) of
        CmpEQ -> case go anext (b :& bnext) (c :& cnext) of
          Refl -> Refl
        CmpGT -> case go anext (b :& bnext) (c :& cnext) of
          Refl -> case applyCmpTransitive (proxyFst a) (proxyFst b) (proxyFst c) of
            Sub Dict -> Refl
        CmpLT -> case compareTypes (proxyFst a) (proxyFst c) of
          CmpEQ -> case go anext (b :& bnext) cnext of
            Refl -> Refl
          CmpLT -> case go (a :& anext) (b :& bnext) cnext of
            Refl -> Refl
          CmpGT -> case go anext (b :& bnext) (c :& cnext) of
            Refl -> Refl
      CmpLT -> case compareTypes (proxyFst b) (proxyFst c) of
        CmpEQ -> case go (a :& anext) bnext cnext of
          Refl -> Refl
        CmpLT -> case go (a :& anext) (b :& bnext) cnext of
          Refl -> case applyCmpTransitive (proxyFst a) (proxyFst b) (proxyFst c) of
            Sub Dict -> Refl
        CmpGT -> case go (a :& anext) bnext (c :& cnext) of
          Refl -> Refl

commutativity :: forall (as :: [(k,*)]) (bs :: [(k,*)]).
  Rec CmpDict as -> Rec CmpDict bs -> Union as bs :~: Union bs as
commutativity = go
  where
  go :: forall (as1 :: [(k,*)]) (bs1 :: [(k,*)]).
        Rec CmpDict as1 -> Rec CmpDict bs1 -> Union as1 bs1 :~: Union bs1 as1
  go RNil RNil = Refl
  go RNil (_ :& bnext) = case go RNil bnext of
    Refl -> Refl
  go (_ :& anext) RNil = case go anext RNil of
    Refl -> Refl
  go (a@(DictFun :: CmpDict a) :& asNext) (b@(DictFun :: CmpDict b) :& bsNext) =
    case compareTypes (Proxy :: Proxy (Fst a)) (Proxy :: Proxy (Fst b)) of
      CmpEQ -> case (eqT :: Maybe (Snd a :~: Snd b)) of
        Nothing -> error "commutativity failure"
        Just Refl -> case go asNext bsNext of
          Refl -> case tupleEquality a b of
            Sub Dict -> Refl
      CmpLT -> case go (a :& asNext) bsNext of
        Refl -> Refl
      CmpGT -> case go asNext (b :& bsNext) of
        Refl -> Refl

rec :: Rec CmpDict ls -> Rec CmpDict rs -> Rec CmpDict (Union ls rs)
rec RNil RNil = RNil
rec (l :& ls) RNil = l :& rec ls RNil
rec RNil (r :& rs) = r :& rec RNil rs
rec ls@(l@DictFun :& lsNext) rs@(r@DictFun :& rsNext) =
  case compareTypes (proxyFst l) (proxyFst r) of
    CmpLT -> r :& rec ls rsNext
    CmpGT -> l :& rec lsNext rs
    CmpEQ -> case eqTProxy (proxySnd l) (proxySnd r) of
      Just Refl -> l :& rec lsNext rsNext
      Nothing -> error "rec: impossible case"


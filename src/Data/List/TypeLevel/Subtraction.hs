module Data.List.TypeLevel.Subtraction where

import           Data.Constraint
import           Data.List.TypeLevel.Cmp
import           Data.List.TypeLevel.Constraint          (RequireEquality)
import           Data.List.TypeLevel.Union               (Union)
import qualified Data.List.TypeLevel.Union               as Union
import           Data.List.TypeLevel.Witness
import qualified Data.List.TypeLevel.Witness.BoundedList as BoundedList
import qualified Data.List.TypeLevel.Witness.OrdList     as OrdList
import           Data.Tuple.TypeLevel                    (Fst, Snd, proxyFst,
                                                          proxySnd,
                                                          tupleEquality)
import           Data.Type.Equality
import           Data.Vinyl.Core                         hiding (Dict)
import           Data.Vinyl.DictFun
import           Unsafe.Coerce                           (unsafeCoerce)

-- This is NOT total.
type family Subtraction (a :: [(k,v)]) (b :: [(k,v)]) :: [(k,v)] where
  Subtraction '[] '[] = '[]
  Subtraction '[] (b ': bs) = Subtraction '[] bs
  Subtraction (a ': as) '[] = a ': Subtraction as '[]
  Subtraction (a ': as) (b ': bs) = SubtractionCmp (Cmp (Fst a) (Fst b)) a as b bs

type family SubtractionCmp (o :: Ordering) (a :: (k,v)) (as :: [(k,v)]) (b :: (k,v)) (bs :: [(k,v)]) where
  SubtractionCmp 'LT a as b bs = Subtraction (a ': as) bs
  SubtractionCmp 'GT a as b bs = a ': Subtraction as (b ': bs)
  SubtractionCmp 'EQ a as b bs = RequireEquality (Snd a) (Snd b) (Subtraction as bs)

-- Write this when I'm feeling less lazy.
lemma2 :: OrdList ls -> OrdList rs -> Rec CmpDict ls -> Rec CmpDict rs
       -> Union ls (Subtraction ls rs) :~: ls
lemma2 _ _ _ _ = unsafeCoerce Refl

-- Look at this for inspiration
lemma1 :: OrdList ls -> OrdList rs -> Rec CmpDict ls -> Rec CmpDict rs
       -> Union ls (Subtraction rs ls) :~: Union ls rs
lemma1 = go
  where
  go :: forall ls rs. OrdList ls -> OrdList rs -> Rec CmpDict ls -> Rec CmpDict rs
     -> Union ls (Subtraction rs ls) :~: Union ls rs
  go OrdListNil OrdListNil RNil RNil = Refl
  go OrdListNil rsOrd RNil (DictFun :& rsNext) =
    case go OrdListNil (OrdList.tail rsOrd) RNil rsNext of
      Refl -> Refl
  go lsOrd OrdListNil (l@DictFun :& lsNext) RNil =
    case leftIdentity (l :& lsNext) of
      Refl -> case Union.rightIdentity (l :& lsNext) of
        Refl -> Refl
  go lsOrd rsOrd (l@DictFun :& lsNext) (r@DictFun :& rsNext) = let
    lsOrdNext = OrdList.tail lsOrd
    rsOrdNext = OrdList.tail rsOrd
    in case compareTypes (proxyFst l) (proxyFst r) of
      CmpLT -> case go lsOrd rsOrdNext (l :& lsNext) rsNext of
        Refl -> Refl
      CmpGT -> case go lsOrdNext rsOrd lsNext (r :& rsNext) of
        Refl -> case upperBound (BoundedList.boundWith l) (r :& rsNext) lsNext rsOrd lsOrdNext of
          BoundedListCons -> Refl
          BoundedListNil -> Refl
      CmpEQ -> case go lsOrdNext rsOrdNext lsNext rsNext of
        Refl -> case eqTProxy (proxySnd l) (proxySnd r) of
          Nothing -> error "lemma1: messed it up"
          Just Refl -> case tupleEquality l r of
            Sub Dict -> case rsOrd of
              OrdListCons _ -> case upperBound (BoundedList.boundWith r) rsNext lsNext rsOrdNext lsOrdNext of
                BoundedListCons -> Refl
              OrdListSingle -> case leftIdentity lsNext of
                Refl -> Refl

dict :: Rec CmpDict ls -> Rec CmpDict rs -> Rec CmpDict (Subtraction ls rs)
dict ls rs = rec ls rs ls

rec :: Rec CmpDict ls -> Rec CmpDict rs -> Rec f ls -> Rec f (Subtraction ls rs)
rec = go
  where
  go :: forall f ls rs. Rec CmpDict ls -> Rec CmpDict rs -> Rec f ls
     -> Rec f (Subtraction ls rs)
  go RNil RNil RNil = RNil
  go (DictFun :& lsCmpNext) RNil (l :& ls) = l :& go lsCmpNext RNil ls
  go RNil (DictFun :& rsCmpNext) RNil = go RNil rsCmpNext RNil
  go lsCmp@(DictFun :& lsCmpNext) rsCmp@(rd@DictFun :& rsCmpNext) (l :& ls) =
    case compareTypes (proxyFst l) (proxyFst rd) of
      CmpGT -> l :& go lsCmpNext rsCmp ls
      CmpLT -> go lsCmp rsCmpNext (l :& ls)
      CmpEQ -> case eqTProxy (proxySnd l) (proxySnd rd) of
        Nothing -> error "subtraction rec: impossible case"
        Just Refl -> go lsCmpNext rsCmpNext ls


sublist :: Rec CmpDict ls -> Rec CmpDict rs -> Sublist ls (Subtraction ls rs)
sublist = go
  where
  go :: forall ls rs. Rec CmpDict ls -> Rec CmpDict rs
     -> Sublist ls (Subtraction ls rs)
  go ls rs = case ls of
    RNil -> case rs of
      RNil -> SublistNil
      _ :& rsNext -> go RNil rsNext
    l@DictFun :& lsNext -> case rs of
      RNil -> SublistBoth (go lsNext RNil)
      r@DictFun :& rsNext -> case compareTypes (proxyFst l) (proxyFst r) of
        CmpGT -> SublistBoth (go lsNext (r :& rsNext))
        CmpLT -> go (l :& lsNext) rsNext
        CmpEQ -> case eqTProxy (proxySnd l) (proxySnd r) of
          Nothing -> error "subtraction sublist type mismatch"
          Just Refl -> SublistSuper (go lsNext rsNext)

zeroIdentity :: Rec proxy xs -> Subtraction xs xs :~: '[]
zeroIdentity RNil = Refl
zeroIdentity (r :& rs) = case selfEquality (proxyFst r) of
  Refl -> case zeroIdentity rs of
    Refl -> Refl

leftIdentity :: Rec proxy xs -> Subtraction '[] xs :~: '[]
leftIdentity RNil = Refl
leftIdentity (_ :& rs) = case leftIdentity rs of
  Refl -> Refl

rightIdentity :: Rec proxy xs -> Subtraction xs '[] :~: xs
rightIdentity RNil = Refl
rightIdentity (_ :& rs) = case rightIdentity rs of
  Refl -> Refl

upperBound2 ::
     BoundedList u as -> BoundedList u bs
  -> Rec CmpDict as -> Rec CmpDict bs
  -> OrdList as -> OrdList bs
  -> (BoundedList u (Subtraction as bs), BoundedList u (Subtraction bs as))
upperBound2 asBound bsBound asCmp bsCmp asOrd bsOrd =
  ( upperBound asBound asCmp bsCmp asOrd bsOrd
  , upperBound bsBound bsCmp asCmp bsOrd asOrd
  )

upperBound :: BoundedList u as -> Rec CmpDict as -> Rec CmpDict bs
  -> OrdList as -> OrdList bs -> BoundedList u (Subtraction as bs)
upperBound = go
  where
  go :: forall u as bs. BoundedList u as -> Rec CmpDict as -> Rec CmpDict bs
     -> OrdList as -> OrdList bs -> BoundedList u (Subtraction as bs)
  go BoundedListNil RNil RNil OrdListNil OrdListNil = BoundedListNil
  go BoundedListCons (_ :& asCmpNext) RNil asOrd OrdListNil =
    case rightIdentity asCmpNext of
      Refl -> BoundedListCons
  go BoundedListNil RNil (_ :& bsCmpNext) OrdListNil bsOrd =
    case leftIdentity bsCmpNext of
      Refl -> BoundedListNil
  go bl@BoundedListCons asCmp@(a@DictFun :& asCmpNext) bsCmp@(b@DictFun :& bsCmpNext) asOrd bsOrd = case asOrd of
    OrdListSingle -> let
      bsOrdNext = OrdList.tail bsOrd
      in case compareTypes (proxyFst a) (proxyFst b) of
        CmpLT -> go bl asCmp bsCmpNext asOrd bsOrdNext
        CmpGT -> BoundedListCons
        CmpEQ -> case leftIdentity bsCmpNext of
          Refl -> case eqTProxy (proxySnd a) (proxySnd b) of
            Just Refl -> BoundedListNil
            Nothing -> error "upperBound: eq refl failure"
    OrdListCons asOrdNext -> let
      bsOrdNext = OrdList.tail bsOrd
      in case compareTypes (proxyFst a) (proxyFst b) of
        CmpLT -> go bl asCmp bsCmpNext asOrd bsOrdNext
        CmpGT -> BoundedListCons
        CmpEQ -> case transitiveLT (proxyFst $ OrdList.head asOrdNext) (proxyFst a) (proxyFst $ BoundedList.getBound bl) of
          Sub Dict -> case eqTProxy (proxySnd a) (proxySnd b) of
            Just Refl -> go BoundedListCons asCmpNext bsCmpNext asOrdNext bsOrdNext
            Nothing -> error "upperBound: eq refl failure"

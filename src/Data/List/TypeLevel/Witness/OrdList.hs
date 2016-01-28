module Data.List.TypeLevel.Witness.OrdList where

import           Prelude                     hiding (head, tail)

import           Data.Constraint
import           Data.List.TypeLevel.Cmp
import           Data.List.TypeLevel.Union   (Union)
import qualified Data.List.TypeLevel.Union   as Union
import           Data.List.TypeLevel.Witness
import           Data.Proxy
import           Data.Tuple.TypeLevel
import           Data.Type.Equality
import           Data.Vinyl.Core             (Rec (..))
import           Data.Vinyl.DictFun

tail :: OrdList (c ': cs) -> OrdList cs
tail OrdListSingle = OrdListNil
tail (OrdListCons x) = x

head :: OrdList (c ': cs) -> Proxy c
head OrdListSingle = Proxy
head (OrdListCons _) = Proxy

removalBounded :: RemoveElem a rs ss -> OrdList (b ': rs) -> BoundedList b ss
removalBounded RemoveElemDone (OrdListCons OrdListSingle) = BoundedListNil
removalBounded RemoveElemDone ol'@(OrdListCons ol''@(OrdListCons ol''')) =
  case transitiveLT (proxyFst $ head ol''') (proxyFst $ head ol'') (proxyFst $ head ol') of
    Sub Dict -> BoundedListCons

remove :: RemoveElem a rs ss -> OrdList rs -> OrdList ss
remove = go
  where
  go :: forall a rs ss. RemoveElem a rs ss -> OrdList rs -> OrdList ss
  go RemoveElemDone OrdListSingle = OrdListNil
  go RemoveElemDone (OrdListCons olNext) = olNext
  go (RemoveElemNext rmNext) ol = case olRes of
    OrdListCons _ -> case removalBounded rmNext ol of
      BoundedListCons -> OrdListCons olRes
    OrdListSingle -> case removalBounded rmNext ol of
      BoundedListCons -> OrdListCons olRes
    where olRes = go rmNext (tail ol)

insert :: InsertElemOrd a rs ss -> OrdList rs -> OrdList ss
insert ieo ol = case ieo of
  InsertElemOrdSpecial s -> case s of
    SpecialInsertSingle -> case ol of
      OrdListNil -> OrdListSingle
    SpecialInsertFirst -> case ol of
      OrdListSingle -> OrdListCons ol
      OrdListCons _ -> OrdListCons ol
  InsertElemOrdRecursive r -> go r ol
  where
  go :: forall a rs ss. RecursiveInsert a rs ss -> OrdList rs -> OrdList ss
  go RecursiveInsertLast OrdListSingle = OrdListCons OrdListSingle
  go RecursiveInsertMiddle (OrdListCons olNext) = OrdListCons (OrdListCons olNext)
  go (RecursiveInsertNext inext) (OrdListCons onext) = case resNext of
    OrdListCons _ -> case recInsertSameHead inext of
      Refl -> OrdListCons resNext
    OrdListSingle -> case recInsertSameHead inext of
      Refl -> OrdListCons resNext
    where resNext = go inext onext

recInsertSameHead :: RecursiveInsert r (a ': rs) (b ': ss) -> a :~: b
recInsertSameHead RecursiveInsertLast = Refl
recInsertSameHead RecursiveInsertMiddle = Refl
recInsertSameHead (RecursiveInsertNext _) = Refl

downgradeInsert :: InsertElemOrd r rs ss -> RemoveElem r ss rs
downgradeInsert ins = case ins of
  InsertElemOrdSpecial s -> case s of
    SpecialInsertSingle -> RemoveElemDone
    SpecialInsertFirst -> RemoveElemDone
  InsertElemOrdRecursive r -> go r
  where
  go :: forall r rs ss. RecursiveInsert r rs ss -> RemoveElem r ss rs
  go RecursiveInsertLast = RemoveElemNext RemoveElemDone
  go RecursiveInsertMiddle = RemoveElemNext RemoveElemDone
  go (RecursiveInsertNext inext) = RemoveElemNext (go inext)

union :: Rec CmpDict ls -> Rec CmpDict rs
      -> OrdList ls -> OrdList rs -> OrdList (Union ls rs)
union = go
  where
  go :: forall ls rs.
        Rec CmpDict ls -> Rec CmpDict rs
     -> OrdList ls -> OrdList rs -> OrdList (Union ls rs)
  go RNil RNil OrdListNil OrdListNil = OrdListNil
  go ls RNil lsOrd OrdListNil = case Union.rightIdentity ls of
    Refl -> lsOrd
  go RNil rs OrdListNil rsOrd = case Union.leftIdentity rs of
    Refl -> rsOrd
  go ls@(l@DictFun :& lsNext) rs@(r@DictFun :& rsNext) lsOrd rsOrd = let
    lsOrdNext = tail lsOrd
    rsOrdNext = tail rsOrd
    in case compareTypes (proxyFst l) (proxyFst r) of
      CmpGT -> case upperBound (toBoundedList lsOrd) BoundedListCons lsNext rs of
        BoundedListNil -> OrdListSingle
        BoundedListCons -> OrdListCons (go lsNext rs lsOrdNext rsOrd)
      CmpLT -> case upperBound BoundedListCons (toBoundedList rsOrd) ls rsNext of
        BoundedListNil -> OrdListSingle
        BoundedListCons -> OrdListCons (go ls rsNext lsOrd rsOrdNext)
      CmpEQ -> case eqTProxy (proxySnd l) (proxySnd r) of
        Nothing -> error "ordlist union: messed up"
        Just Refl -> case tupleEquality l r of
          Sub Dict -> case upperBound (toBoundedList lsOrd) (toBoundedList rsOrd) lsNext rsNext of
            BoundedListNil -> OrdListSingle
            BoundedListCons -> OrdListCons (go lsNext rsNext lsOrdNext rsOrdNext)

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

lemma1 :: Sublist super sub -> OrdList (b ': super) -> BoundedList b sub
lemma1 SublistNil OrdListSingle = BoundedListNil
lemma1 (SublistBoth s') (OrdListCons o') = BoundedListCons
lemma1 (SublistSuper SublistNil) o@(OrdListCons OrdListSingle) = BoundedListNil
lemma1 (SublistSuper s') o@(OrdListCons o'@(OrdListCons o'')) =
  case transitiveLT (proxyFst $ head o'') (proxyFst $ head o') (proxyFst $ head o) of
    Sub Dict -> lemma1 s' (OrdListCons o'')

upperBound ::
     BoundedList u as -> BoundedList u bs
  -> Rec CmpDict as -> Rec CmpDict bs
  -> BoundedList u (Union as bs)
upperBound = go
  where
  go :: forall u as bs. BoundedList u as -> BoundedList u bs
     -> Rec CmpDict as -> Rec CmpDict bs
     -> BoundedList u (Union as bs)
  go BoundedListNil BoundedListNil RNil RNil = BoundedListNil
  go BoundedListNil BoundedListCons RNil (_ :& _) = BoundedListCons
  go BoundedListCons BoundedListNil (_ :& _) RNil = BoundedListCons
  go bl@BoundedListCons br@BoundedListCons asCmp@(a@DictFun :& asCmpNext) bsCmp@(b@DictFun :& bsCmpNext) =
    case compareTypes (proxyFst a) (proxyFst b) of
      CmpLT -> BoundedListCons
      CmpGT -> BoundedListCons
      CmpEQ -> case eqTProxy (proxySnd a) (proxySnd b) of
        Just Refl -> BoundedListCons
        Nothing -> error "upperBound: eq refl failure"



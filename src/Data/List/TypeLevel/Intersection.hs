module Data.List.TypeLevel.Intersection where

import           Data.Constraint
import           Data.List.TypeLevel.Cmp
import           Data.List.TypeLevel.Subtraction         (Subtraction)
import qualified Data.List.TypeLevel.Subtraction         as Subtraction
import           Data.List.TypeLevel.Union               (Union)
import           Data.List.TypeLevel.Witness
import qualified Data.List.TypeLevel.Witness.BoundedList as BoundedList
import qualified Data.List.TypeLevel.Witness.OrdList     as OrdList
import           Data.Tuple.TypeLevel
import           Data.Type.Equality
import           Data.Vinyl.Core                         hiding (Dict)
import           Data.Vinyl.DictFun                      (DictFun (..))

type Intersection as bs = Subtraction as (Subtraction as bs)

-- This function is unusual because it is left biased. Maybe not.
rec :: Rec CmpDict ls -> Rec CmpDict rs -> Rec f ls -> Rec f (Intersection ls rs)
rec lsCmp rsCmp ls = Subtraction.rec lsCmp (Subtraction.dict lsCmp rsCmp) ls

dict :: Rec CmpDict ls -> Rec CmpDict rs -> Rec CmpDict (Intersection ls rs)
dict ls rs = rec ls rs ls

commutativity :: Rec CmpDict as -> Rec CmpDict bs -> OrdList as -> OrdList bs
  -> Intersection as bs :~: Intersection bs as
commutativity = go
  where
  go :: forall as bs. Rec CmpDict as -> Rec CmpDict bs -> OrdList as -> OrdList bs
     -> Intersection as bs :~: Intersection bs as
  go RNil RNil OrdListNil OrdListNil = Refl
  go as RNil _ OrdListNil = case Subtraction.leftIdentity as of
    Refl -> case Subtraction.rightIdentity as of
      Refl -> case Subtraction.zeroIdentity as of
        Refl -> Refl
  go (a@DictFun :& asNext) (b@DictFun :& bsNext) asOrd bsOrd = let
    asOrdNext = OrdList.tail asOrd
    bsOrdNext = OrdList.tail bsOrd
    in case compareTypes (proxyFst a) (proxyFst b) of
      CmpEQ -> case eqTProxy (proxySnd a) (proxySnd b) of
        Nothing -> error "intersection commutativity failure"
        Just Refl -> case tupleEquality a b of
          Sub Dict -> case go asNext bsNext asOrdNext bsOrdNext of
            Refl -> case Subtraction.upperBound2 (OrdList.toBoundedList asOrd) (OrdList.toBoundedList bsOrd) asNext bsNext asOrdNext bsOrdNext of
              (BoundedListCons,BoundedListCons) -> Refl
              (BoundedListCons,BoundedListNil)  -> Refl
              (BoundedListNil,BoundedListCons)  -> Refl
              (BoundedListNil,BoundedListNil)   -> Refl
      CmpLT -> case go (a :& asNext) bsNext asOrd bsOrdNext of
        Refl -> case selfEquality (proxyFst b) of
          Refl -> Refl
      CmpGT -> case go asNext (b :& bsNext) asOrdNext bsOrd of
        Refl -> case selfEquality (proxyFst a) of
          Refl -> Refl


-- proof :: BoundedList b as -> proxy1 bs
--       -> Subtraction as (b ': bs) :~: Subtraction as bs
-- proof b _ = case b of
--   BoundedListNil -> Refl
--   BoundedListCons -> Refl


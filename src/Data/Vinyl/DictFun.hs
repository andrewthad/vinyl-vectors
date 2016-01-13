module Data.Vinyl.DictFun where

import           Data.Constraint
import           Data.List.TypeLevel.Constraint (ListAll)
import           Data.Proxy
import           Data.Vinyl.Core                hiding (Dict)
import           Data.Vinyl.TypeLevel           (RecAll)
import           GHC.Exts                       (Constraint)

data DictFun (c :: k -> Constraint) (a :: k) where
  DictFun :: c a => DictFun c a

dictFunOf :: Proxy c -> Dict (c a) -> DictFun c a
dictFunOf _ Dict = DictFun

reifyDictFun :: ListAll rs c => proxy1 c -> Rec proxy2 rs -> Rec (DictFun c) rs
reifyDictFun _ RNil = RNil
reifyDictFun p (_ :& rs) = DictFun :& reifyDictFun p rs

weakenRecDictFun :: forall c1 c2 proxy rs.
     proxy c2
  -> (forall a. c1 a :- c2 a)
  -> Rec (DictFun c1) rs
  -> Rec (DictFun c2) rs
weakenRecDictFun _ _ RNil = RNil
weakenRecDictFun p ent ((DictFun :: DictFun c1 r) :& rs) = case (ent :: (c1 r :- c2 r))  of
  Sub Dict -> DictFun :& weakenRecDictFun p ent rs

weakenRecDictFun2 :: forall c1 c2 proxy rs.
     (forall a. c1 a :- c2 a)
  -> Rec (DictFun c1) rs
  -> Rec (DictFun c2) rs
weakenRecDictFun2 _ RNil = RNil
weakenRecDictFun2 ent ((DictFun :: DictFun c1 r) :& rs) = case (ent :: (c1 r :- c2 r))  of
  Sub Dict -> DictFun :& weakenRecDictFun2 ent rs

dictFunToRecAll :: forall c1 c2 proxy proxy2 f rs.
     proxy f
  -> proxy2 c2
  -> (forall a. c1 a :- c2 (f a))
  -> Rec (DictFun c1) rs
  -> Dict (RecAll f rs c2)
dictFunToRecAll _ _ _ RNil = Dict
dictFunToRecAll p c2 ent ((DictFun :: DictFun c1 r) :& rs) = case (ent :: (c1 r :- c2 (f r)))  of
  Sub Dict -> case dictFunToRecAll p c2 ent rs of
    Dict -> Dict

dictFunToListAll :: forall c rs.
     Rec (DictFun c) rs
  -> Dict (ListAll rs c)
dictFunToListAll RNil = Dict
dictFunToListAll (DictFun :& rs) = case dictFunToListAll rs of
    Dict -> Dict




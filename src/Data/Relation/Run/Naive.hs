{-# LANGUAGE PolyKinds #-}

module Data.Relation.Run.Naive
  ( run
  , runTest
  ) where

import           Control.Arrow                    (second)
import           Data.Constraint
import           Data.List.TypeLevel
import           Data.List.TypeLevel.Cmp
import           Data.List.TypeLevel.Constraint   ((:&:))
import           Data.List.TypeLevel.Intersection (Intersection)
import qualified Data.List.TypeLevel.Intersection as Intersection
import           Data.List.TypeLevel.Subtraction  (Subtraction)
import qualified Data.List.TypeLevel.Subtraction  as Subtraction
import           Data.List.TypeLevel.Union        (Union)
import qualified Data.List.TypeLevel.Union        as Union
import           Data.List.TypeLevel.Witness
import           Data.Map                         (Map)
import qualified Data.Map                         as Map
import           Data.Proxy
import           Data.Relation
import           Data.Relation.Backend            (Naive (..), Test (..))
import           Data.Relation.Backend
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import           Data.Tagged.Functor
import           Data.Tuple.TypeLevel
import           Data.Type.Equality
import           Data.Typeable
import           Data.TypeString
import           Data.Vector.Vinyl.Default.Types
import           Data.Vinyl.Class.Implication
import           Data.Vinyl.Core                  hiding (Dict)
import           Data.Vinyl.DictFun
import           Data.Vinyl.Functor               (Identity (..))
import           Data.Vinyl.Named

-- newtype R rs = R (Set (Rec (TaggedFunctor Identity) rs))

runTest :: RelOp Naive rs -> IO (Test rs)
runTest = return . Test . Set.toList . getNaive . run

run :: RelOp Naive rs -> Naive rs
run = go
  where
  go :: forall rs. RelOp Naive rs -> Naive rs
  go (RelTable _ _ r) = r
  go (RelProject s relOp) =
    case recDictFunToDict $ projectRec s $ relOpOrd relOp of
      Dict -> case listAllToTaggedRecAll (Proxy :: Proxy Ord) (Proxy :: Proxy Identity) subProxyRec (Sub Dict) of
        Sub Dict -> case recAllOrd (Proxy :: Proxy (TaggedFunctor Identity)) subProxyRec of
          Sub Dict -> case r of
            (Naive recs) -> Naive $ Set.map (projectRec s) recs
    where r = go relOp
          subProxyRec = sublistSubToRec s
  go (RelRestrict sublist pred relOp) = case go relOp of
    Naive set -> Naive $ Set.filter (predToPredicate sublist pred (relOpOrd relOp)) set
  go (RelJoin relOpA relOpB) = Naive $ naturalJoinExplicit
    (relOpOrdered relOpA) (relOpOrdered relOpB)
    (relOpConstraints relOpA) (relOpConstraints relOpB)
    (getNaive $ go relOpA) (getNaive $ go relOpB)


naturalJoinExplicit :: forall ls rs is bs lsOnly rsOnly.
  ( lsOnly ~ Subtraction ls rs
  , rsOnly ~ Subtraction rs ls
  , is ~ Intersection ls rs
  , bs ~ Union ls rs
  ) => OrdList ls
    -> OrdList rs
    -> Rec (DictFun MinimalConstraints) ls
    -> Rec (DictFun MinimalConstraints) rs
    -> Set (Rec (TaggedFunctor Identity) ls)
    -> Set (Rec (TaggedFunctor Identity) rs)
    -> Set (Rec (TaggedFunctor Identity) bs)
naturalJoinExplicit lsOrd rsOrd lsDicts rsDicts lsRecs rsRecs = finalSet
  where
  proxyTfi     = Proxy :: Proxy (TaggedFunctor Identity)
  proxyOrd     = Proxy :: Proxy Ord
  proxyOrdDict = Proxy :: Proxy (ConstrainSnd Ord)
  proxyCmpDict = Proxy :: Proxy (ConstrainFst TypeString :&: ConstrainSnd Typeable)
  finalSet :: Set (Rec (TaggedFunctor Identity) bs)
  finalSet = case dictFunToRecAll proxyTfi proxyOrd (Sub Dict) bsOrdDicts of
    Dict -> case recAllOrd proxyTfi bsCmp of
      Sub Dict -> Set.fromList finalList
  finalList :: [Rec (TaggedFunctor Identity) bs]
  finalList = map untriple joinedList
  merge1 :: Rec (TaggedFunctor Identity) is -> Rec (TaggedFunctor Identity) lsOnly
         -> Rec (TaggedFunctor Identity) ls
  merge1 is lsOnly = case Subtraction.lemma1 lsOnlyOrd lsOrd lsOnlyCmp lsCmp of
    Refl -> case Union.commutativity lsOnlyCmp lsCmp of
      Refl -> case Union.commutativity isCmp lsOnlyCmp of
        Refl -> case Subtraction.lemma2 lsOrd rsOrd lsCmp rsCmp of
          Refl -> Union.rec isCmp lsOnlyCmp is lsOnly
  merge2 :: Rec (TaggedFunctor Identity) ls -> Rec (TaggedFunctor Identity) rsOnly
         -> Rec (TaggedFunctor Identity) bs
  merge2 ls rsOnly = case Subtraction.lemma1 lsOrd rsOrd lsCmp rsCmp of
    Refl -> Union.rec lsCmp rsOnlyCmp ls rsOnly
  untriple :: ( Rec (TaggedFunctor Identity) is
              , Rec (TaggedFunctor Identity) lsOnly
              , Rec (TaggedFunctor Identity) rsOnly
              ) -> Rec (TaggedFunctor Identity) bs
  untriple (is, lsOnly, rsOnly) = merge2 (merge1 is lsOnly) rsOnly
  joinedList :: [ ( Rec (TaggedFunctor Identity) is
                  , Rec (TaggedFunctor Identity) lsOnly
                  , Rec (TaggedFunctor Identity) rsOnly
                  ) ]
  joinedList = case isOrdDict of
    Dict -> id
      $ (=<<) (\(k,(ls,rs)) -> (,,) <$> pure k <*> ls <*> rs)
      $ Map.toList
      $ Map.intersectionWith (,) lsMap rsMap
  lsMap :: Map (Rec (TaggedFunctor Identity) is) [Rec (TaggedFunctor Identity) lsOnly]
  lsMap = case isOrdDict of
    Dict -> Map.fromListWith (++) . map (second pure . lsSplit) . Set.toList $ lsRecs
  rsMap :: Map (Rec (TaggedFunctor Identity) is) [Rec (TaggedFunctor Identity) rsOnly]
  rsMap = case isOrdDict of
    Dict -> Map.fromListWith (++) . map (second pure . rsSplit) . Set.toList $ rsRecs
  lsSplit :: Rec p ls -> (Rec p is, Rec p lsOnly)
  lsSplit = (,)
    <$> Intersection.rec lsCmp rsCmp
    <*> Subtraction.rec lsCmp rsCmp
  rsSplit :: Rec p rs -> (Rec p is, Rec p rsOnly)
  rsSplit r = case Intersection.commutativity lsCmp rsCmp lsOrd rsOrd of
    Refl -> ($ r) $ (,)
      <$> Intersection.rec rsCmp lsCmp
      <*> Subtraction.rec rsCmp lsCmp
  isOrdDict :: Dict (Ord (Rec (TaggedFunctor Identity) is))
  isOrdDict = case dictFunToRecAll proxyTfi proxyOrd (Sub Dict) isOrdDicts of
    Dict -> case recAllOrd proxyTfi isOrdDicts of
      Sub Dict -> Dict
  isOrdDicts :: Rec (DictFun (ConstrainSnd Ord)) is
  isOrdDicts = id
    $ projectRec (Subtraction.sublist lsCmp (Subtraction.dict lsCmp rsCmp))
    $ weakenRecDictFun (Proxy :: Proxy (ConstrainSnd Ord)) (Sub Dict)
    $ lsDicts
  lsOrdDicts :: Rec (DictFun (ConstrainSnd Ord)) ls
  lsOrdDicts = weakenRecDictFun proxyOrdDict (Sub Dict) lsDicts
  rsOrdDicts :: Rec (DictFun (ConstrainSnd Ord)) rs
  rsOrdDicts = weakenRecDictFun proxyOrdDict (Sub Dict) rsDicts
  bsOrdDicts :: Rec (DictFun (ConstrainSnd Ord)) bs
  bsOrdDicts = Union.rec lsCmp rsCmp lsOrdDicts rsOrdDicts
  rsOnlyCmp :: Rec CmpDict rsOnly
  rsOnlyCmp = Subtraction.dict rsCmp lsCmp
  lsOnlyCmp :: Rec CmpDict lsOnly
  lsOnlyCmp = Subtraction.dict lsCmp rsCmp
  isCmp :: Rec CmpDict is
  isCmp = Intersection.dict lsCmp rsCmp
  lsCmp :: Rec CmpDict ls
  lsCmp = weakenRecDictFun proxyCmpDict (Sub Dict) lsDicts
  rsCmp :: Rec CmpDict rs
  rsCmp = weakenRecDictFun proxyCmpDict (Sub Dict) rsDicts
  bsCmp :: Rec CmpDict bs
  bsCmp = Union.dict lsCmp rsCmp
  lsOnlyOrd :: OrdList lsOnly
  lsOnlyOrd = error "uetn"
  rsOnlyOrd :: OrdList rsOnly
  rsOnlyOrd = error "uetn"
  -- lsMap :: [(Rec (TaggedFunctor Identity) is, Rec (TaggedFunctor Identity) ls)]
  -- lsMap = map lsSplit $ Set.toList lsRecs


predToPredicate :: Sublist super sub -> Pred sub -> Rec (DictFun (ConstrainSnd Ord)) super -> Rec (TaggedFunctor Identity) super -> Bool
predToPredicate = go
  where
  go :: forall super sub. Sublist super sub -> Pred sub -> Rec (DictFun (ConstrainSnd Ord)) super -> Rec (TaggedFunctor Identity) super -> Bool
  go sublist (PredNot pred) dicts rec = not $ go sublist pred dicts rec
  go sublist (PredEqCols _) dicts rec = case projectRec sublist dicts of
    DictFun :& DictFun :& RNil -> case projectRec sublist rec of
      TaggedFunctor (Identity u) :& TaggedFunctor (Identity v) :& RNil -> u == v
  go sublist (PredEqValue v) dicts rec = case projectRec sublist dicts of
    DictFun :& RNil -> case projectRec sublist rec of
      TaggedFunctor (Identity u) :& RNil -> u == v
  go sublist (PredAnd sub1 sub2 pred1 pred2) dicts rec = pred1Result && pred2Result
    where
    pred1Result = go (sublistTransitive sublist sub1) pred1 dicts rec
    pred2Result = go (sublistTransitive sublist sub2) pred2 dicts rec
  go sublist (PredOr sub1 sub2 pred1 pred2) dicts rec = pred1Result || pred2Result
    where
    pred1Result = go (sublistTransitive sublist sub1) pred1 dicts rec
    pred2Result = go (sublistTransitive sublist sub2) pred2 dicts rec

relationArity :: Naive rs -> Int
relationArity (Naive s) = Set.size s


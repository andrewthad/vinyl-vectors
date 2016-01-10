{-# LANGUAGE PolyKinds #-}

module Data.Relation.Run.Naive
  ( run
  , runTest
  ) where

import           Data.Constraint
import           Data.List.TypeLevel
import           Data.List.TypeLevel.Subtraction (Subtraction)
import           Data.List.TypeLevel.Union       (Union)
import           Data.Proxy
import           Data.Relation
import           Data.Relation.Backend           (Naive (..), Test (..))
import           Data.Relation.Backend
import           Data.Set                        (Set)
import qualified Data.Set                        as Set
import           Data.Tagged.Functor
import           Data.Tuple.TypeLevel
import           Data.Vector.Vinyl.Default.Types
import           Data.Vinyl.Class.Implication
import           Data.Vinyl.Core                 hiding (Dict)
import           Data.Vinyl.DictFun
import           Data.Vinyl.Functor              (Identity (..))
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
    (relOpConstraints relOpA) (relOpConstraints relOpB)
    (getNaive $ go relOpA) (getNaive $ go relOpB)


naturalJoinExplicit :: forall ls rs lsOnly rsOnly.
  ( lsOnly ~ Subtraction ls rs
  , rsOnly ~ Subtraction rs ls
  ) => Rec (DictFun MinimalConstraints) ls
    -> Rec (DictFun MinimalConstraints) rs
    -> Set (Rec (TaggedFunctor Identity) ls)
    -> Set (Rec (TaggedFunctor Identity) rs)
    -> Set (Rec (TaggedFunctor Identity) (Union ls rs))
naturalJoinExplicit lCols rCols lsRecs rsRecs = error "write me"
  where
  proxyLs = Proxy :: Proxy ls
  proxyRs = Proxy :: Proxy rs

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


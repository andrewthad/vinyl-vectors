{-# LANGUAGE PolyKinds #-}

module Data.Relation.Run.Naive 
  ( run
  ) where

import Data.Relation
import Data.Tagged.Functor
import Data.List.TypeLevel
import Data.Vinyl.Core hiding (Dict)
import Data.Vector.Vinyl.Default.Types
import Data.Vinyl.Named
import Data.Vinyl.Functor (Identity(..))
import Data.Constraint
import Data.Set (Set)
import Data.Proxy
import Data.Vinyl.Class.Implication
import qualified Data.Set as Set

newtype R rs = R (Set (Rec (TaggedFunctor Identity) rs))

run :: RelOp R rs -> Relation R rs
run = go
  where
  go :: forall rs. RelOp R rs -> Relation R rs
  go (RelTable _ _ r) = r
  go (RelProject s relOp) = case subProxyRec of
    RNil -> RelationNull (R Set.empty) (if relationArity r > 0 then NullRelOne else NullRelZero)
    _ :& _ -> case recDictFunToDict $ projectRec s $ relOpOrd relOp of
      Dict -> case listAllToTaggedRecAll (Proxy :: Proxy Ord) (Proxy :: Proxy Identity) subProxyRec (Sub Dict) of
        Sub Dict -> case recAllOrd (Proxy :: Proxy (TaggedFunctor Identity)) subProxyRec of
          Sub Dict -> case r of
            RelationPresent (R recs) -> RelationPresent . R $ Set.map (projectRec s) recs -- VT.toRec $ VT.map (projectRec s) (VT.fromRec vecs)
    where r = go relOp
          subProxyRec = sublistSubToRec s

relationArity :: Relation R rs -> Int
relationArity r = case r of
  RelationNull _ a -> nullRelArityToInt a
  RelationPresent (R v) -> Set.size v


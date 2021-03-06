{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeOperators    #-}
module Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Join where

import           Control.Monad                                              (guard)
import           Control.Monad.Primitive                                    (PrimMonad, PrimState)
import           Control.Monad.ST                                           (ST, runST)
import           Data.Constraint
import           Data.Function                                              (on)
import qualified Data.List                                                  as List
import           Data.List.TypeLevel.Constraint                             (ListAll)
import           Data.Primitive.MutVar                                      (newMutVar, readMutVar, writeMutVar)
import           Data.Proxy                                                 (Proxy (Proxy))
import qualified Data.Vector.Algorithms.Merge                               as Merge
import qualified Data.Vector.Generic                                        as G
import qualified Data.Vector.Generic.Mutable                                as GM
import qualified Data.Vector.Hybrid                                         as Hybrid
import qualified Data.Vector.Hybrid.Internal                                as Hybrid
import qualified Data.Vector.Hybrid.Mutable                                 as MHybrid
import qualified Data.Vector.Unboxed                                        as U
import qualified Data.Vector.Unboxed.Mutable                                as UM
import           Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Implication (listAllVector)
import qualified Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Internal    as Vinyl
import           Data.Vector.Vinyl.Default.Types                            (HasDefaultVector, VectorVal)
import           Data.Vinyl.Class.Implication                               (listAllOrd)
import           Data.Vinyl.Core                                            (Rec (..))
import           Data.Vinyl.Functor                                         (Identity)
import           Data.Vinyl.TypeLevel                                       (RecAll)

defSort :: (PrimMonad m, GM.MVector v e, Ord e) => v (PrimState m) e -> m ()
defSort = Merge.sort

defSortBy :: (PrimMonad m, GM.MVector v e) => (e -> e -> Ordering) -> v (PrimState m) e -> m ()
defSortBy = Merge.sortBy

uniq :: (G.Vector v a, Eq a) => v a -> v a
uniq v = if G.length v > 0
  then runST $ do
    let initVal = v G.! 0
    m <- GM.new (G.length v)
    GM.write m 0 initVal
    mlen <- uniqHelper 1 1 initVal v m
    G.freeze $ GM.slice 0 mlen m
  else G.empty

uniqHelper :: (GM.MVector u a, G.Vector v a, Eq a, PrimMonad m)
  => Int -> Int -> a -> v a -> u (PrimState m) a -> m Int
uniqHelper i j prev v m = if (i < G.length v)
  then let current = v G.! i in
    if current == prev
      then uniqHelper (i + 1) j prev v m
      else do
        GM.write m j current
        uniqHelper (i + 1) (j + 1) current v m
  else return j

uniqNaive :: Eq a => [a] -> [a]
uniqNaive = map List.head . List.group

-- This is a poorly performing but certainly correct
-- version of the algorithm. Notice that the produced
-- ordering of the indices may differ.
fullJoinIndicesNaive :: Ord a => [a] -> [a] -> [(Int,Int)]
fullJoinIndicesNaive as bs = do
  (ia,a) <- List.sortBy (compare `on` snd) (zip (enumFrom 0) as)
  (ib,b) <- List.sortBy (compare `on` snd) (zip (enumFrom 0) bs)
  guard (a == b)
  return (ia,ib)

-- Demands that records are identical. This step must be performed
-- after a projection step. This destroys the input vectors.
fullJoinIndices ::
  ( PrimMonad m
  , s ~ PrimState m
  , GM.MVector v a
  , Ord a
  )
  => v s a
  -> v s a
  -> m (Hybrid.MVector U.MVector U.MVector s (Int,Int))
fullJoinIndices as bs = do
  ias <- pairWithIndices as
  ibs <- pairWithIndices bs
  sortWithIndices ias
  sortWithIndices ibs
  matchingIndices ias ibs

indexMany :: ( G.Vector v a ) => U.Vector Int -> v a -> v a
indexMany ixs xs = runST $ do
  res <- GM.new (U.length ixs)
  flip U.imapM_ ixs $ \i ix -> do
    GM.write res i (xs G.! ix)
  G.freeze res

indexManyPredicate :: ( G.Vector v a )
  => (a -> Bool) -> U.Vector Int -> v a -> U.Vector Bool
indexManyPredicate predicate ixs xs = runST $ do
  res <- UM.new (U.length ixs)
  flip U.imapM_ ixs $ \i ix -> do
    UM.write res i (predicate (xs G.! ix))
  U.freeze res

fullJoinIndicesImmutable ::
  ( G.Vector v a
  , Ord a
  )
  => v a
  -> v a
  -> Hybrid.Vector U.Vector U.Vector (Int,Int)
fullJoinIndicesImmutable as bs = runST $ do
  mas <- G.thaw as
  mbs <- G.thaw bs
  r <- fullJoinIndices mas mbs
  G.freeze r

recFullJoinIndicesImmutable :: forall rs z zs.
  ( ListAll rs Ord
  , ListAll rs HasDefaultVector
  -- , ListAll rs
  , rs ~ (z ': zs)
  )
  => Rec VectorVal rs
  -> Rec VectorVal rs
  -> Hybrid.Vector U.Vector U.Vector (Int,Int)
recFullJoinIndicesImmutable as bs =
  case listAllOrd (Proxy :: Proxy Identity) as (Sub Dict) of
    Sub Dict -> case listAllVector as of
      Sub Dict -> fullJoinIndicesImmutable (Vinyl.V as) (Vinyl.V bs)

-- The input vectors must already be sorted from
-- low to high. Otherwise, this may crash.
matchingIndices ::
  ( GM.MVector v a
  , GM.MVector u b
  , GM.MVector w c
  , PrimMonad m
  , s ~ PrimState m
  , Ord a
  )
  => Hybrid.MVector u v s (b, a)
  -> Hybrid.MVector w v s (c, a)
  -> m (Hybrid.MVector u w s (b,c))
matchingIndices as bs = do
  iaRef <- newMutVar 0
  ibRef <- newMutVar 0
  iaWalkRef <- newMutVar 0
  ibWalkRef <- newMutVar 0
  irRef <- newMutVar 0
  rinit <- MHybrid.new initialSize
  rref  <- newMutVar rinit
  let appendRes v = do
        rbefore <- readMutVar rref
        ir <- readMutVar irRef
        r <- case compare ir (MHybrid.length rbefore) of
          EQ -> do
            r' <- MHybrid.grow rbefore ir
            writeMutVar rref r'
            return r'
          LT -> return rbefore
          GT -> error "matchingIndices: invariant violated"
        writeMutVar irRef (ir + 1)
        MHybrid.write r ir v -- (traceShowId v)
  whileM_
    ( do ia <- readMutVar iaRef
         ib <- readMutVar ibRef
         return (ia < alen && ib < blen)
    )
    ( do ia <- readMutVar iaRef
         ib <- readMutVar ibRef
         (iaOriginal,arec) <- MHybrid.read as ia
         (ibOriginal,brec) <- MHybrid.read bs ib
         case compare arec brec of
           LT -> writeMutVar iaRef (ia + 1)
           GT -> writeMutVar ibRef (ib + 1)
           EQ -> do
             appendRes (iaOriginal,ibOriginal)
             -- Iterate over b
             writeMutVar ibWalkRef (ib + 1)
             whileM_
               ( do ibWalk <- readMutVar ibWalkRef
                    case compare ibWalk blen of
                      LT -> do
                        (_,brecNext) <- MHybrid.read bs ibWalk
                        return (brecNext == arec)
                      EQ -> return False
                      GT -> error "ib walk: invariant violated"
               )
               ( do ibWalk <- readMutVar ibWalkRef
                    (ibOriginalNext,_brecNext) <- MHybrid.read bs ibWalk
                    appendRes (iaOriginal, ibOriginalNext)
                    writeMutVar ibWalkRef (ibWalk + 1)
               )
             -- Iterate over a
             writeMutVar iaWalkRef (ia + 1)
             whileM_
               ( do iaWalk <- readMutVar iaWalkRef
                    case compare iaWalk alen of
                      LT -> do
                        (_,arecNext) <- MHybrid.read as iaWalk
                        return (arecNext == brec)
                      EQ -> return False
                      GT -> error "ia walk: invariant violated"
               )
               ( do iaWalk <- readMutVar iaWalkRef
                    (iaOriginalNext,_arecNext) <- MHybrid.read as iaWalk
                    appendRes (iaOriginalNext, ibOriginal)
                    writeMutVar iaWalkRef (iaWalk + 1)
               )
             writeMutVar iaRef (ia + 1)
             writeMutVar ibRef (ib + 1)
    )
  r <- readMutVar rref
  ir <- readMutVar irRef
  return (MHybrid.slice 0 ir r)
  where
  initialSize = 4 -- change to 64
  alen = MHybrid.length as
  blen = MHybrid.length bs

whileM_ :: (Monad m) => m Bool -> m a -> m ()
whileM_ p f = go
  where
  go = do
    x <- p
    if x
      then f >> go
      else return ()


-- gives us the freedom to use anything as indices
-- instead of just Ints
matchingIndicesExtraImmutable ::
  ( G.Vector v a
  , G.Vector u b
  , G.Vector w c
  , Ord a
  )
  => Hybrid.Vector u v (b,a)
  -> Hybrid.Vector w v (c,a)
  -> Hybrid.Vector u w (b,c)
matchingIndicesExtraImmutable a b = runST $ do
  ma <- Hybrid.thaw a
  mb <- Hybrid.thaw b
  mr <- matchingIndices ma mb
  Hybrid.freeze mr

pairWithIndices ::
  ( PrimMonad m
  , s ~ PrimState m
  , GM.MVector v a
  )
  => v s a
  -> m (Hybrid.MVector U.MVector v s (Int, a))
pairWithIndices v = do
  let total = GM.length v
  mv <- U.thaw (U.fromList (enumFromTo 0 (total - 1)))
  return (Hybrid.MV mv v)

sortWithIndices ::
  ( Ord a
  , GM.MVector v a
  , GM.MVector u i
  , PrimMonad m
  , s ~ PrimState m
  )
  => Hybrid.MVector u v s (i,a)
  -> m ()
sortWithIndices v = defSortBy (\(_,a) (_,b) -> compare a b) v


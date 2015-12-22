{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Join where

import Control.Monad.Primitive (PrimMonad,PrimState)
import qualified Data.Vector.Algorithms.Merge as Merge
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Hybrid          as Hybrid
import qualified Data.Vector.Hybrid.Internal as Hybrid
import qualified Data.Vector.Hybrid.Mutable  as MHybrid
import qualified Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Internal as Vinyl
import qualified Data.List as List
import Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Implication (listAllVector)
import Data.Vector.Vinyl.Default.Types (HasDefaultVector,VectorVal)
import Data.Vector.Vinyl.TypeLevel (ListAll)
import Data.Vinyl.Core       (Rec(..))
import Data.Vinyl.Functor    (Identity)
import Data.Vinyl.TypeLevel  (RecAll)
import Data.Vinyl.Class.Implication (listAllOrd)
import Control.Monad.ST      (ST,runST)
import Data.Primitive.MutVar (newMutVar, readMutVar, writeMutVar)
import Control.Monad         (guard)
import Data.Function         (on)
import Data.Constraint
import Data.Proxy            (Proxy(Proxy))

defSort :: (PrimMonad m, GM.MVector v e, Ord e) => v (PrimState m) e -> m ()
defSort = Merge.sort

defSortBy :: (PrimMonad m, GM.MVector v e) => (e -> e -> Ordering) -> v (PrimState m) e -> m ()
defSortBy = Merge.sortBy

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
  , PrimMonad m
  , s ~ PrimState m
  , Ord a
  )
  => Hybrid.MVector U.MVector v s (Int, a)
  -> Hybrid.MVector U.MVector v s (Int, a)
  -> m (Hybrid.MVector U.MVector U.MVector s (Int,Int))
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


-- matchingIndices ::
--   ( G.MVector v a
--   , PrimMonad m
--   , s ~ PrimState m
--   )
--   => Int -- left index
--   -> Int -- right index
--   -> Int -- resulting vector index
--   -> Int -- size of result so far
--   -> Hybrid.MVector U.MVector v s (Int, Rec Identity rs)
--   -> Hybrid.MVector U.MVector v s (Int, Rec Identity rs)
--   -> Hybrid.MVector U.MVector U.MVector (Int,Int)
--   -> m ()
-- matchingIndices ia ib ir rsize a b r = do
--   rsizeNext <- if rsize == ir 
--     then do
--       Hybrid.grow r rsize
--       return (rsize * 2)
--     else return rsize
--   
--   matchingIndices rsizeNext

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
  , PrimMonad m
  , s ~ PrimState m
  )
  => Hybrid.MVector U.MVector v s (Int,a)
  -> m ()
sortWithIndices v = defSortBy (\(_,a) (_,b) -> compare a b) v
 

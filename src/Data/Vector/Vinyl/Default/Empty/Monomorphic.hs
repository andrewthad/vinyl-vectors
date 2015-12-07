{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
-----------------------------------------------------------------------------
-- |
-- Copyright   :  Andrew Martin
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Andrew Martin <andrew.thaddeus@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- There are two vector types provided by this module: 'Vector' and
-- 'MVector'. They must be parameterized over a type that unifies
-- with 'Rec Identity rs'. An example would be:
--
-- > foo :: Vector (Rec Identity '[Int,Char,Bool])
-- 
-- This vector stores records that have an 'Int', a 'Char', and a 'Bool'.
-----------------------------------------------------------------------------
module Data.Vector.Vinyl.Default.Empty.Monomorphic
  ( Vector, MVector

  -- * Accessors

  -- ** Length information
  , length, null

  -- ** Indexing
  , (!), (!?), head, last
  , unsafeIndex, unsafeHead, unsafeLast

  -- ** Monadic indexing
  , indexM, headM, lastM
  , unsafeIndexM, unsafeHeadM, unsafeLastM

  -- ** Extracting subvectors (slicing)
  , slice, init, tail, take, drop, splitAt
  , unsafeSlice, unsafeInit, unsafeTail, unsafeTake, unsafeDrop

  -- * Construction

  -- ** Initialisation
  , empty, singleton, replicate, generate, iterateN

  -- ** Monadic initialisation
  , replicateM, generateM, create

  -- ** Unfolding
  , unfoldr, unfoldrN
  , constructN, constructrN

  -- -- ** Enumeration
  -- , enumFromN, enumFromStepN, enumFromTo, enumFromThenTo

  -- ** Concatenation
  , cons, snoc, (++), concat

  -- ** Restricting memory usage
  , force

  -- * Modifying vectors

  -- ** Bulk updates
  , (//)
  , unsafeUpd
  -- , update_, unsafeUpdate_

  -- ** Accumulations
  , accum, unsafeAccum
  -- , accumulate_, unsafeAccumulate_

  -- ** Permutations
  , reverse
  -- , backpermute, unsafeBackpermute

  -- ** Safe destructive updates
  , modify

  -- * Elementwise operations

  -- ** Mapping
  , map, imap, concatMap

  -- ** Monadic mapping
  , mapM, mapM_, forM, forM_

  -- ** Zipping - Omitted due to me being lazy
  -- , zipWith, zipWith3, zipWith4, zipWith5, zipWith6
  -- , izipWith, izipWith3, izipWith4, izipWith5, izipWith6

  -- ** Monadic zipping
  , zipWithM, zipWithM_

  -- * Working with predicates

  -- ** Filtering
  , filter, ifilter, filterM
  , takeWhile, dropWhile

  -- ** Partitioning
  , partition, unstablePartition, span, break

  -- ** Searching
  , elem, notElem, find, findIndex
  , elemIndex
  -- , findIndices, elemIndices

  -- * Folding
  , foldl, foldl1, foldl', foldl1', foldr, foldr1, foldr', foldr1'
  , ifoldl, ifoldl', ifoldr, ifoldr'

  -- ** Specialised folds
  , all, any
  -- , sum, product
  , maximum, maximumBy, minimum, minimumBy
  , minIndex, minIndexBy, maxIndex, maxIndexBy

  -- ** Monadic folds
  , foldM, foldM', fold1M, fold1M'
  , foldM_, foldM'_, fold1M_, fold1M'_

  -- * Prefix sums (scans)
  , prescanl, prescanl'
  , postscanl, postscanl'
  , scanl, scanl', scanl1, scanl1'
  , prescanr, prescanr'
  , postscanr, postscanr'
  , scanr, scanr', scanr1, scanr1'

  -- ** Lists
  , toList, fromList, fromListN

  -- ** Other vector types
  , G.convert

  -- ** Mutable vectors
  , freeze, thaw, copy, unsafeFreeze, unsafeThaw, unsafeCopy
  ) where

import Control.Monad.Primitive
import Control.Monad.ST
import Data.Vector.Vinyl.Default.Empty.Monomorphic.Internal
import Data.Vinyl.Core
import Data.Vinyl.Functor (Identity(..))
import qualified Data.Vector.Generic as G
import Prelude hiding ( length, null,
                        replicate, (++), concat,
                        head, last,
                        init, tail, take, drop, splitAt, reverse,
                        map, concatMap,
                        zipWith, zipWith3, zip, zip3, unzip, unzip3,
                        filter, takeWhile, dropWhile, span, break,
                        elem, notElem,
                        foldl, foldl1, foldr, foldr1,
                        all, any, sum, product, minimum, maximum,
                        scanl, scanl1, scanr, scanr1,
                        enumFromTo, enumFromThenTo,
                        mapM, mapM_ )


-- Length
-- ------

-- | /O(1)/ Yield the length of the vector.
length :: Vector (Rec Identity rs) -> Int
length (V i _) = i
{-# INLINE length #-}

-- | /O(1)/ Test whether a vector if empty
null :: Vector (Rec Identity rs) -> Bool
null (V i _) = i == 0
{-# INLINE null #-}


-- Indexing
-- --------

-- | O(1) Indexing
(!) :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Int -> Rec Identity rs
(!) = (G.!)
{-# INLINE (!) #-}

-- | O(1) Safe indexing
(!?) :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Int -> Maybe (Rec Identity rs)
(!?) = (G.!?)
{-# INLINE (!?) #-}

-- | /O(1)/ First element
head :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Rec Identity rs
head = G.head
{-# INLINE head #-}

-- | /O(1)/ Last element
last :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Rec Identity rs
last = G.last
{-# INLINE last #-}


-- | /O(1)/ Unsafe indexing without bounds checking
unsafeIndex :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Int -> Rec Identity rs
{-# INLINE unsafeIndex #-}
unsafeIndex = G.unsafeIndex

-- | /O(1)/ First element without checking if the vector is empty
unsafeHead :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Rec Identity rs
{-# INLINE unsafeHead #-}
unsafeHead = G.unsafeHead

-- | /O(1)/ Last element without checking if the vector is empty
unsafeLast :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Rec Identity rs
{-# INLINE unsafeLast #-}
unsafeLast = G.unsafeLast

-- Monadic indexing
-- ----------------

-- | /O(1)/ Indexing in a monad.
--
-- The monad allows operations to be strict in the vector when necessary.
-- Suppose vector copying is implemented like this:
--
-- > copy mv v = ... write mv i (v ! i) ...
--
-- For lazy vectors, @v ! i@ would not be evaluated which means that @mv@
-- would unnecessarily retain a reference to @v@ in each element written.
--
-- With 'indexM', copying can be implemented like this instead:
--
-- > copy mv v = ... do
-- >                   x <- indexM v i
-- >                   write mv i x
--
-- Here, no references to @v@ are retained because indexing (but /not/ the
-- elements) is evaluated eagerly.
--
indexM :: (Monad m, G.Vector Vector (Rec Identity rs))
  => Vector (Rec Identity rs) -> Int -> m (Rec Identity rs)
indexM = G.indexM
{-# INLINE indexM #-}

-- | /O(1)/ First element of a vector in a monad. See 'indexM' for an
-- explanation of why this is useful.
headM :: (Monad m, G.Vector Vector (Rec Identity rs))
  => Vector (Rec Identity rs) -> m (Rec Identity rs)
headM = G.headM
{-# INLINE headM #-}

-- | /O(1)/ Last element of a vector in a monad. See 'indexM' for an
-- explanation of why this is useful.
lastM :: (Monad m, G.Vector Vector (Rec Identity rs))
  => Vector (Rec Identity rs) -> m (Rec Identity rs)
lastM = G.lastM
{-# INLINE lastM #-}

-- | /O(1)/ Indexing in a monad without bounds checks. See 'indexM' for an
-- explanation of why this is useful.
unsafeIndexM :: (Monad m, G.Vector Vector (Rec Identity rs))
  => Vector (Rec Identity rs) -> Int -> m (Rec Identity rs)
unsafeIndexM = G.unsafeIndexM
{-# INLINE unsafeIndexM #-}

-- | /O(1)/ First element in a monad without checking for empty vectors.
-- See 'indexM' for an explanation of why this is useful.
unsafeHeadM :: (Monad m, G.Vector Vector (Rec Identity rs))
  => Vector (Rec Identity rs) -> m (Rec Identity rs)
unsafeHeadM = G.unsafeHeadM
{-# INLINE unsafeHeadM #-}

-- | /O(1)/ Last element in a monad without checking for empty vectors.
-- See 'indexM' for an explanation of why this is useful.
unsafeLastM :: (Monad m, G.Vector Vector (Rec Identity rs))
  => Vector (Rec Identity rs) -> m (Rec Identity rs)
unsafeLastM = G.unsafeLastM
{-# INLINE unsafeLastM #-}

-- Extracting subvectors (slicing)
-- -------------------------------

-- | /O(1)/ Yield a slice of the vector without copying it. The vector must
-- contain at least @i+n@ elements.
slice :: G.Vector Vector (Rec Identity rs)
      => Int   -- ^ @i@ starting index
      -> Int   -- ^ @n@ length
      -> Vector (Rec Identity rs)
      -> Vector (Rec Identity rs)
slice = G.slice
{-# INLINE slice #-}

-- | /O(1)/ Yield all but the last element without copying. The vector may not
-- be empty.
init :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Vector (Rec Identity rs)
init = G.init
{-# INLINE init #-}

-- | /O(1)/ Yield all but the first element without copying. The vector may not
-- be empty.
tail :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Vector (Rec Identity rs)
tail = G.tail
{-# INLINE tail #-}

-- | /O(1)/ Yield at the first @n@ elements without copying. The vector may
-- contain less than @n@ elements in which case it is returned unchanged.
take :: G.Vector Vector (Rec Identity rs)
  => Int -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
take = G.take
{-# INLINE take #-}

-- | /O(1)/ Yield all but the first @n@ elements without copying. The vector may
-- contain less than @n@ elements in which case an empty vector is returned.
drop :: G.Vector Vector (Rec Identity rs)
  => Int -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
drop = G.drop
{-# INLINE drop #-}

-- | /O(1)/ Yield the first @n@ elements paired with the remainder without copying.
--
-- Note that @'splitAt' n v@ is equivalent to @('take' n v, 'drop' n v)@
-- but slightly more efficient.
splitAt :: G.Vector Vector (Rec Identity rs)
  => Int -> Vector (Rec Identity rs) -> (Vector (Rec Identity rs), Vector (Rec Identity rs))
splitAt = G.splitAt
{-# INLINE splitAt #-}

-- | /O(1)/ Yield a slice of the vector without copying. The vector must
-- contain at least @i+n@ elements but this is not checked.
unsafeSlice :: G.Vector Vector (Rec Identity rs)
  => Int   -- ^ @i@ starting index
                       -> Int   -- ^ @n@ length
                       -> Vector (Rec Identity rs)
                       -> Vector (Rec Identity rs)
unsafeSlice = G.unsafeSlice
{-# INLINE unsafeSlice #-}

-- | /O(1)/ Yield all but the last element without copying. The vector may not
-- be empty but this is not checked.
unsafeInit :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Vector (Rec Identity rs)
unsafeInit = G.unsafeInit
{-# INLINE unsafeInit #-}

-- | /O(1)/ Yield all but the first element without copying. The vector may not
-- be empty but this is not checked.
unsafeTail :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Vector (Rec Identity rs)
unsafeTail = G.unsafeTail
{-# INLINE unsafeTail #-}

-- | /O(1)/ Yield the first @n@ elements without copying. The vector must
-- contain at least @n@ elements but this is not checked.
unsafeTake :: G.Vector Vector (Rec Identity rs)
  => Int -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
unsafeTake = G.unsafeTake
{-# INLINE unsafeTake #-}

-- | /O(1)/ Yield all but the first @n@ elements without copying. The vector
-- must contain at least @n@ elements but this is not checked.
unsafeDrop :: G.Vector Vector (Rec Identity rs)
  => Int -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
unsafeDrop = G.unsafeDrop
{-# INLINE unsafeDrop #-}

-- Initialisation
-- --------------

-- | /O(1)/ Empty vector
empty :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs)
empty = G.empty
{-# INLINE empty #-}

-- | /O(1)/ Vector with exactly one element
singleton :: G.Vector Vector (Rec Identity rs)
  => Rec Identity rs -> Vector (Rec Identity rs)
singleton = G.singleton
{-# INLINE singleton #-}

-- | /O(n)/ Vector of the given length with the same value in each position
replicate :: G.Vector Vector (Rec Identity rs)
  => Int -> Rec Identity rs -> Vector (Rec Identity rs)
replicate = G.replicate
{-# INLINE replicate #-}

-- | /O(n)/ Construct a vector of the given length by applying the function to
-- each index
generate :: G.Vector Vector (Rec Identity rs)
  => Int -> (Int -> Rec Identity rs) -> Vector (Rec Identity rs)
generate = G.generate
{-# INLINE generate #-}

-- | /O(n)/ Apply function n times to value. Zeroth element is original value.
iterateN :: G.Vector Vector (Rec Identity rs)
  => Int -> (Rec Identity rs -> Rec Identity rs) -> Rec Identity rs -> Vector (Rec Identity rs)
iterateN = G.iterateN
{-# INLINE iterateN #-}

-- Unfolding
-- ---------

-- | /O(n)/ Construct a vector by repeatedly applying the generator function
-- to a seed. The generator function yields 'Just' the next element and the
-- new seed or 'Nothing' if there are no more elements.
--
-- > unfoldr (\n -> if n == 0 then Nothing else Just (n,n-1)) 10
-- >  = <10,9,8,7,6,5,4,3,2,1>
unfoldr :: G.Vector Vector (Rec Identity rs)
  => (c -> Maybe (Rec Identity rs, c)) -> c -> Vector (Rec Identity rs)
unfoldr = G.unfoldr
{-# INLINE unfoldr #-}

-- | /O(n)/ Construct a vector with at most @n@ by repeatedly applying the
-- generator function to the a seed. The generator function yields 'Just' the
-- next element and the new seed or 'Nothing' if there are no more elements.
--
-- > unfoldrN 3 (\n -> Just (n,n-1)) 10 = <10,9,8>
unfoldrN :: G.Vector Vector (Rec Identity rs)
  => Int -> (c -> Maybe (Rec Identity rs, c)) -> c -> Vector (Rec Identity rs)
unfoldrN = G.unfoldrN
{-# INLINE unfoldrN #-}

-- | /O(n)/ Construct a vector with @n@ elements by repeatedly applying the
-- generator function to the already constructed part of the vector.
--
-- > constructN 3 f = let a = f <> ; b = f <a> ; c = f <a,b> in f <a,b,c>
--
constructN :: G.Vector Vector (Rec Identity rs)
  => Int -> (Vector (Rec Identity rs) -> Rec Identity rs) -> Vector (Rec Identity rs)
constructN = G.constructN
{-# INLINE constructN #-}

-- | /O(n)/ Construct a vector with @n@ elements from right to left by
-- repeatedly applying the generator function to the already constructed part
-- of the vector.
--
-- > constructrN 3 f = let a = f <> ; b = f<a> ; c = f <b,a> in f <c,b,a>
--
constructrN :: G.Vector Vector (Rec Identity rs)
  => Int -> (Vector (Rec Identity rs) -> Rec Identity rs) -> Vector (Rec Identity rs)
constructrN = G.constructrN
{-# INLINE constructrN #-}

-- Concatenation
-- -------------

-- | /O(n)/ Prepend an element
cons :: G.Vector Vector (Rec Identity rs)
  => Rec Identity rs -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
{-# INLINE cons #-}
cons = G.cons

-- | /O(n)/ Append an element
snoc :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Rec Identity rs -> Vector (Rec Identity rs)
{-# INLINE snoc #-}
snoc = G.snoc

infixr 5 ++
-- | /O(m+n)/ Concatenate two vectors
(++) :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
{-# INLINE (++) #-}
(++) = (G.++)

-- | /O(n)/ Concatenate all vectors in the list
concat :: G.Vector Vector (Rec Identity rs)
  => [Vector (Rec Identity rs)] -> Vector (Rec Identity rs)
{-# INLINE concat #-}
concat = G.concat

-- Monadic initialisation
-- ----------------------

-- | /O(n)/ Execute the monadic action the given number of times and store the
-- results in a vector.
replicateM :: (Monad m, G.Vector Vector (Rec Identity rs))
  => Int -> m (Rec Identity rs) -> m (Vector (Rec Identity rs))
replicateM = G.replicateM
{-# INLINE replicateM #-}

-- | /O(n)/ Construct a vector of the given length by applying the monadic
-- action to each index
generateM :: (Monad m, G.Vector Vector (Rec Identity rs))
  => Int -> (Int -> m (Rec Identity rs)) -> m (Vector (Rec Identity rs))
generateM = G.generateM
{-# INLINE generateM #-}

-- | Execute the monadic action and freeze the resulting vector.
--
-- @
-- create (do { v \<- new 2; write v 0 \'a\'; write v 1 \'b\'; return v }) = \<'a','b'\>
-- @
create :: G.Vector Vector (Rec Identity rs)
  => (forall s. ST s (G.Mutable Vector s (Rec Identity rs))) -> Vector (Rec Identity rs)
-- NOTE: eta-expanded due to http://hackage.haskell.org/trac/ghc/ticket/4120
create p = G.create p
{-# INLINE create #-}

-- Restricting memory usage
-- ------------------------

-- | /O(n)/ Yield the argument but force it not to retain any extra memory,
-- possibly by copying it.
--
-- This is especially useful when dealing with slices. For example:
--
-- > force (slice 0 2 <huge vector>)
--
-- Here, the slice retains a reference to the huge vector. Forcing it creates
-- a copy of just the elements that belong to the slice and allows the huge
-- vector to be garbage collected.
force :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Vector (Rec Identity rs)
force = G.force
{-# INLINE force #-}

-- Bulk updates
-- ------------

-- | /O(m+n)/ For each pair @(i,a)@ from the list, replace the vector
-- element at position @i@ by @a@.
--
-- > <5,9,2,7> // [(2,1),(0,3),(2,8)] = <3,9,8,7>
--
(//) :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs)   -- ^ initial vector (of length @m@)
                -> [(Int, Rec Identity rs)]                          -- ^ list of index/value pairs (of length @n@)
                -> Vector (Rec Identity rs)
(//) = (G.//)
{-# INLINE (//) #-}

-- | Same as ('//') but without bounds checking.
unsafeUpd :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> [(Int, Rec Identity rs)] -> Vector (Rec Identity rs)
unsafeUpd = G.unsafeUpd
{-# INLINE unsafeUpd #-}

-- Accumulations
-- -------------

-- | /O(m+n)/ For each pair @(i,c)@ from the list, replace the vector element
-- @a@ at position @i@ by @f a c@.
--
-- > accum (+) <5,9,2> [(2,4),(1,6),(0,3),(1,7)] = <5+3, 9+6+7, 2+4>
accum :: G.Vector Vector (Rec Identity rs)
      => (Rec Identity rs -> c -> Rec Identity rs) -- ^ accumulating function @f@
      -> Vector (Rec Identity rs)       -- ^ initial vector (of length @m@)
      -> [(Int,c)]               -- ^ list of index/value pairs (of length @n@)
      -> Vector (Rec Identity rs)
accum = G.accum
{-# INLINE accum #-}

-- | Same as 'accum' but without bounds checking.
unsafeAccum :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> c -> Rec Identity rs) -> Vector (Rec Identity rs) -> [(Int,c)] -> Vector (Rec Identity rs)
unsafeAccum = G.unsafeAccum
{-# INLINE unsafeAccum #-}


-- Permutations
-- ------------

-- | /O(n)/ Reverse a vector
reverse :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> Vector (Rec Identity rs)
{-# INLINE reverse #-}
reverse = G.reverse

-- Safe destructive updates
-- ------------------------

-- | Apply a destructive operation to a vector. The operation will be
-- performed in place if it is safe to do so and will modify a copy of the
-- vector otherwise.
--
-- @
-- modify (\\v -> write v 0 \'x\') ('replicate' 3 \'a\') = \<\'x\',\'a\',\'a\'\>
-- @
modify :: (G.Vector Vector (Rec Identity rs))
       => (forall s. G.Mutable Vector s (Rec Identity rs) -> ST s ())
       -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
{-# INLINE modify #-}
modify p = G.modify p

-- Mapping
-- -------

-- | /O(n)/ Map a function over a vector
map :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
    => (Rec Identity rs -> Rec Identity ss) -> Vector (Rec Identity rs) -> Vector (Rec Identity ss)
map = G.map
{-# INLINE map #-}

-- | /O(n)/ Apply a function to every element of a vector and its index
imap :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
     => (Int -> Rec Identity rs -> Rec Identity ss)
     -> Vector (Rec Identity rs) -> Vector (Rec Identity ss)
imap = G.imap
{-# INLINE imap #-}

-- | Map a function over a vector and concatenate the results.
concatMap :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
          => (Rec Identity rs -> Vector (Rec Identity ss)) -> Vector (Rec Identity rs) -> Vector (Rec Identity ss)
concatMap = G.concatMap
{-# INLINE concatMap #-}

-- Monadic mapping
-- ---------------

-- | /O(n)/ Apply the monadic action to all elements of the vector, yielding a
-- vector of results
mapM :: (Monad m, G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> m (Rec Identity ss)) -> Vector (Rec Identity rs) -> m (Vector (Rec Identity ss))
mapM = G.mapM
{-# INLINE mapM #-}

-- | /O(n)/ Apply the monadic action to all elements of a vector and ignore the
-- results
mapM_ :: (Monad m, G.Vector Vector (Rec Identity rs))
  => (Rec Identity rs -> m b) -> Vector (Rec Identity rs) -> m ()
mapM_ = G.mapM_
{-# INLINE mapM_ #-}

-- | /O(n)/ Apply the monadic action to all elements of the vector, yielding a
-- vector of results. Equvalent to @flip 'mapM'@.
forM :: (Monad m, G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => Vector (Rec Identity rs) -> (Rec Identity rs -> m (Rec Identity ss)) -> m (Vector (Rec Identity ss))
forM = G.forM
{-# INLINE forM #-}

-- | /O(n)/ Apply the monadic action to all elements of a vector and ignore the
-- results. Equivalent to @flip 'mapM_'@.
forM_ :: (Monad m, G.Vector Vector (Rec Identity rs))
  => Vector (Rec Identity rs) -> (Rec Identity rs -> m b) -> m ()
forM_ = G.forM_
{-# INLINE forM_ #-}

-- Zipping
-- -------

--   -- | /O(min(m,n))/ Zip two vectors with the given function.
--   zipWith :: ( G.Vector u a, G.Vector v a'
--              , G.Vector u b, G.Vector v b'
--              , G.Vector u c, G.Vector v c'
--              ) => ((a,a') -> (b,b') -> (c,c'))
--                -> Vector u v (a,a') -> Vector u v (b,b') -> Vector u v (c,c')
--   zipWith = G.zipWith
--   {-# INLINE zipWith #-}
--   
--   -- | Zip three vectors with the given function.
--   
--   zipWith3 :: ( G.Vector u a, G.Vector v a'
--               , G.Vector u b, G.Vector v b'
--               , G.Vector u c, G.Vector v c'
--               , G.Vector u d, G.Vector v d'
--               ) => ((a,a') -> (b,b') -> (c,c') -> (d, d'))
--                 -> Vector u v (a,a') -> Vector u v (b,b') -> Vector u v (c,c') -> Vector u v (d,d')
--   zipWith3 = G.zipWith3
--   {-# INLINE zipWith3 #-}
--   
--   zipWith4 :: ( G.Vector u a, G.Vector v a'
--               , G.Vector u b, G.Vector v b'
--               , G.Vector u c, G.Vector v c'
--               , G.Vector u d, G.Vector v d'
--               , G.Vector u e, G.Vector v e'
--               ) => ((a,a') -> (b,b') -> (c,c') -> (d, d') -> (e,e'))
--                 -> Vector u v (a,a') -> Vector u v (b,b') -> Vector u v (c,c') -> Vector u v (d,d') -> Vector u v (e,e')
--   zipWith4 = G.zipWith4
--   {-# INLINE zipWith4 #-}
--   
--   zipWith5 :: ( G.Vector u a, G.Vector v a'
--               , G.Vector u b, G.Vector v b'
--               , G.Vector u c, G.Vector v c'
--               , G.Vector u d, G.Vector v d'
--               , G.Vector u e, G.Vector v e'
--               , G.Vector u f, G.Vector v f'
--               ) => ((a,a') -> (b,b') -> (c,c') -> (d, d') -> (e,e') -> (f,f'))
--                 -> Vector u v (a,a') -> Vector u v (b,b') -> Vector u v (c,c') -> Vector u v (d,d') -> Vector u v (e,e') -> Vector u v (f,f')
--   zipWith5 = G.zipWith5
--   {-# INLINE zipWith5 #-}
--   
--   zipWith6 :: ( G.Vector u a, G.Vector v a'
--               , G.Vector u b, G.Vector v b'
--               , G.Vector u c, G.Vector v c'
--               , G.Vector u d, G.Vector v d'
--               , G.Vector u e, G.Vector v e'
--               , G.Vector u f, G.Vector v f'
--               , G.Vector u g, G.Vector v g'
--               ) => ((a,a') -> (b,b') -> (c,c') -> (d, d') -> (e,e') -> (f,f') -> (g,g'))
--                 -> Vector u v (a,a') -> Vector u v (b,b') -> Vector u v (c,c') -> Vector u v (d,d') -> Vector u v (e,e') -> Vector u v (f,f') -> Vector u v (g,g')
--   zipWith6 = G.zipWith6
--   {-# INLINE zipWith6 #-}
--   
--   -- | /O(min(m,n))/ Zip two vectors with a function that also takes the
--   -- elements' indices.
--   izipWith :: ( G.Vector u a, G.Vector v a'
--               , G.Vector u b, G.Vector v b'
--               , G.Vector u c, G.Vector v c'
--               ) => (Int -> (a,a') -> (b,b') -> (c,c'))
--                 -> Vector u v (a,a') -> Vector u v (b,b') -> Vector u v (c,c')
--   izipWith = G.izipWith
--   {-# INLINE izipWith #-}
--   
--   -- | Zip three vectors and their indices with the given function.
--   izipWith3 :: ( G.Vector u a, G.Vector v a'
--               , G.Vector u b, G.Vector v b'
--               , G.Vector u c, G.Vector v c'
--               , G.Vector u d, G.Vector v d'
--               ) => (Int -> (a,a') -> (b,b') -> (c,c') -> (d, d'))
--                 -> Vector u v (a,a') -> Vector u v (b,b') -> Vector u v (c,c') -> Vector u v (d,d')
--   izipWith3 = G.izipWith3
--   {-# INLINE izipWith3 #-}
--   
--   izipWith4 :: ( G.Vector u a, G.Vector v a'
--               , G.Vector u b, G.Vector v b'
--               , G.Vector u c, G.Vector v c'
--               , G.Vector u d, G.Vector v d'
--               , G.Vector u e, G.Vector v e'
--               ) => (Int -> (a,a') -> (b,b') -> (c,c') -> (d, d') -> (e,e'))
--                 -> Vector u v (a,a') -> Vector u v (b,b') -> Vector u v (c,c') -> Vector u v (d,d') -> Vector u v (e,e')
--   izipWith4 = G.izipWith4
--   {-# INLINE izipWith4 #-}
--   
--   izipWith5 :: ( G.Vector u a, G.Vector v a'
--               , G.Vector u b, G.Vector v b'
--               , G.Vector u c, G.Vector v c'
--               , G.Vector u d, G.Vector v d'
--               , G.Vector u e, G.Vector v e'
--               , G.Vector u f, G.Vector v f'
--               ) => (Int -> (a,a') -> (b,b') -> (c,c') -> (d, d') -> (e,e') -> (f,f'))
--                 -> Vector u v (a,a') -> Vector u v (b,b') -> Vector u v (c,c') -> Vector u v (d,d') -> Vector u v (e,e') -> Vector u v (f,f')
--   izipWith5 = G.izipWith5
--   {-# INLINE izipWith5 #-}
--   
--   izipWith6 :: ( G.Vector u a, G.Vector v a'
--               , G.Vector u b, G.Vector v b'
--               , G.Vector u c, G.Vector v c'
--               , G.Vector u d, G.Vector v d'
--               , G.Vector u e, G.Vector v e'
--               , G.Vector u f, G.Vector v f'
--               , G.Vector u g, G.Vector v g'
--               ) => (Int -> (a,a') -> (b,b') -> (c,c') -> (d, d') -> (e,e') -> (f,f') -> (g,g'))
--                 -> Vector u v (a,a') -> Vector u v (b,b') -> Vector u v (c,c') -> Vector u v (d,d') -> Vector u v (e,e') -> Vector u v (f,f') -> Vector u v (g,g')
--   izipWith6 = G.izipWith6
--   {-# INLINE izipWith6 #-}

-- Monadic zipping
-- ---------------

-- | /O(min(m,n))/ Zip the two vectors with the monadic action and yield a
-- vector of results
zipWithM :: (Monad m, G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss), G.Vector Vector (Rec Identity ts))
         => (Rec Identity rs -> Rec Identity ss -> m (Rec Identity ts)) -> Vector (Rec Identity rs) -> Vector (Rec Identity ss) -> m (Vector (Rec Identity ts))
zipWithM = G.zipWithM
{-# INLINE zipWithM #-}

-- | /O(min(m,n))/ Zip the two vectors with the monadic action and ignore the
-- results
zipWithM_ :: (Monad m, G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
          => (Rec Identity rs -> Rec Identity ss -> m e) -> Vector (Rec Identity rs) -> Vector (Rec Identity ss)-> m ()
zipWithM_ = G.zipWithM_
{-# INLINE zipWithM_ #-}

-- Filtering
-- ---------

-- | /O(n)/ Drop elements that do not satisfy the predicate
filter :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Bool) -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
filter = G.filter
{-# INLINE filter #-}

-- | /O(n)/ Drop elements that do not satisfy the predicate which is applied to
-- values and their indices
ifilter :: G.Vector Vector (Rec Identity rs)
  => (Int -> Rec Identity rs -> Bool) -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
ifilter = G.ifilter
{-# INLINE ifilter #-}

-- | /O(n)/ Drop elements that do not satisfy the monadic predicate
filterM :: (Monad m, G.Vector Vector (Rec Identity rs))
  => (Rec Identity rs -> m Bool) -> Vector (Rec Identity rs) -> m (Vector (Rec Identity rs))
filterM = G.filterM
{-# INLINE filterM #-}

-- | /O(n)/ Yield the longest prefix of elements satisfying the predicate
-- without copying.
takeWhile :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Bool) -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
takeWhile = G.takeWhile
{-# INLINE takeWhile #-}

-- | /O(n)/ Drop the longest prefix of elements that satisfy the predicate
-- without copying.
dropWhile :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Bool) -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
dropWhile = G.dropWhile
{-# INLINE dropWhile #-}


-- Parititioning
-- -------------

-- | /O(n)/ Split the vector in two parts, the first one containing those
-- elements that satisfy the predicate and the second one those that don't. The
-- relative order of the elements is preserved at the cost of a sometimes
-- reduced performance compared to 'unstablePartition'.
partition :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Bool) -> Vector (Rec Identity rs) -> (Vector (Rec Identity rs), Vector (Rec Identity rs))
{-# INLINE partition #-}
partition = G.partition

-- | /O(n)/ Split the vector in two parts, the first one containing those
-- elements that satisfy the predicate and the second one those that don't.
-- The order of the elements is not preserved but the operation is often
-- faster than 'partition'.
unstablePartition :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Bool) -> Vector (Rec Identity rs) -> (Vector (Rec Identity rs), Vector (Rec Identity rs))
{-# INLINE unstablePartition #-}
unstablePartition = G.unstablePartition

-- | /O(n)/ Split the vector into the longest prefix of elements that satisfy
-- the predicate and the rest without copying.
span :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Bool) -> Vector (Rec Identity rs) -> (Vector (Rec Identity rs), Vector (Rec Identity rs))
{-# INLINE span #-}
span = G.span

-- | /O(n)/ Split the vector into the longest prefix of elements that do not
-- satisfy the predicate and the rest without copying.
break :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Bool) -> Vector (Rec Identity rs) -> (Vector (Rec Identity rs), Vector (Rec Identity rs))
{-# INLINE break #-}
break = G.break

-- Searching
-- ---------

infix 4 `elem`
-- | /O(n)/ Check if the vector contains an element
elem :: (G.Vector Vector (Rec Identity rs), Eq (Rec Identity rs))
  => Rec Identity rs -> Vector (Rec Identity rs) -> Bool
elem = G.elem
{-# INLINE elem #-}

infix 4 `notElem`
-- | /O(n)/ Check if the vector does not contain an element (inverse of 'elem')
notElem :: (G.Vector Vector (Rec Identity rs), Eq (Rec Identity rs))
  => Rec Identity rs -> Vector (Rec Identity rs) -> Bool
notElem = G.notElem
{-# INLINE notElem #-}

-- | /O(n)/ Yield 'Just' the first element matching the predicate or 'Nothing'
-- if no such element exists.
find :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Bool) -> Vector (Rec Identity rs) -> Maybe (Rec Identity rs)
find = G.find
{-# INLINE find #-}

-- | /O(n)/ Yield 'Just' the index of the first element matching the predicate
-- or 'Nothing' if no such element exists.
findIndex :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Bool) -> Vector (Rec Identity rs) -> Maybe Int
findIndex = G.findIndex
{-# INLINE findIndex #-}

{-
-- | /O(n)/ Yield the indices of elements satisfying the predicate in ascending
-- order.
findIndices :: ((a, b) -> Bool) -> Vector (Rec Identity rs) -> Vector u v Int
findIndices = G.findIndices
{-# INLINE findIndices #-}
-}

-- | /O(n)/ Yield 'Just' the index of the first occurence of the given element or
-- 'Nothing' if the vector does not contain the element. This is a specialised
-- version of 'findIndex'.
elemIndex :: (G.Vector Vector (Rec Identity rs), Eq (Rec Identity rs))
  => Rec Identity rs -> Vector (Rec Identity rs) -> Maybe Int
elemIndex = G.elemIndex
{-# INLINE elemIndex #-}

{-
-- | /O(n)/ Yield the indices of all occurences of the given element in
-- ascending order. This is a specialised version of 'findIndices'.
elemIndices :: (a, b) -> Vector (Rec Identity rs) -> Vector Int
elemIndices = G.elemIndices
{-# INLINE elemIndices #-}
-}

-- Folding
-- -------

-- | /O(n)/ Left fold
foldl :: G.Vector Vector (Rec Identity rs)
  => (r -> Rec Identity rs -> r) -> r -> Vector (Rec Identity rs) -> r
foldl = G.foldl
{-# INLINE foldl #-}

-- | /O(n)/ Left fold on non-empty vectors
foldl1 :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Rec Identity rs -> Rec Identity rs) -> Vector (Rec Identity rs) -> Rec Identity rs
foldl1 = G.foldl1
{-# INLINE foldl1 #-}

-- | /O(n)/ Left fold with strict accumulator
foldl' :: G.Vector Vector (Rec Identity rs)
  => (r -> Rec Identity rs -> r) -> r -> Vector (Rec Identity rs) -> r
foldl' = G.foldl'
{-# INLINE foldl' #-}

-- | /O(n)/ Left fold on non-empty vectors with strict accumulator
foldl1' :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Rec Identity rs -> Rec Identity rs) -> Vector (Rec Identity rs) -> Rec Identity rs
foldl1' = G.foldl1'
{-# INLINE foldl1' #-}

-- | /O(n)/ Right fold
foldr :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> r -> r) -> r -> Vector (Rec Identity rs) -> r
foldr = G.foldr
{-# INLINE foldr #-}

-- | /O(n)/ Right fold on non-empty vectors
foldr1 :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Rec Identity rs -> Rec Identity rs) -> Vector (Rec Identity rs) -> Rec Identity rs
foldr1 = G.foldr1
{-# INLINE foldr1 #-}

-- | /O(n)/ Right fold with a strict accumulator
foldr' :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> r -> r) -> r -> Vector (Rec Identity rs) -> r
foldr' = G.foldr'
{-# INLINE foldr' #-}

-- | /O(n)/ Right fold on non-empty vectors with strict accumulator
foldr1' :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Rec Identity rs -> Rec Identity rs) -> Vector (Rec Identity rs) -> Rec Identity rs
foldr1' = G.foldr1'
{-# INLINE foldr1' #-}

-- | /O(n)/ Left fold (function applied to each element and its index)
ifoldl :: G.Vector Vector (Rec Identity rs)
  => (r -> Int -> Rec Identity rs -> r) -> r -> Vector (Rec Identity rs) -> r
ifoldl = G.ifoldl
{-# INLINE ifoldl #-}

-- | /O(n)/ Left fold with strict accumulator (function applied to each element
-- and its index)
ifoldl' :: G.Vector Vector (Rec Identity rs)
  => (r -> Int -> Rec Identity rs -> r) -> r -> Vector (Rec Identity rs) -> r
ifoldl' = G.ifoldl'
{-# INLINE ifoldl' #-}

-- | /O(n)/ Right fold (function applied to each element and its index)
ifoldr :: G.Vector Vector (Rec Identity rs)
  => (Int -> Rec Identity rs -> r -> r) -> r -> Vector (Rec Identity rs) -> r
ifoldr = G.ifoldr
{-# INLINE ifoldr #-}

-- | /O(n)/ Right fold with strict accumulator (function applied to each
-- element and its index)
ifoldr' :: G.Vector Vector (Rec Identity rs)
  => (Int -> Rec Identity rs -> r -> r) -> r -> Vector (Rec Identity rs) -> r
ifoldr' = G.ifoldr'
{-# INLINE ifoldr' #-}

-- Specialised folds
-- -----------------

-- | /O(n)/ Check if all elements satisfy the predicate.
all :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Bool) -> Vector (Rec Identity rs) -> Bool
{-# INLINE all #-}
all = G.all

-- | /O(n)/ Check if any element satisfies the predicate.
any :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Bool) -> Vector (Rec Identity rs) -> Bool
{-# INLINE any #-}
any = G.any

{-
-- | /O(n)/ Compute the sum of the elements
sum :: Vector (Rec Identity rs) -> (a, b)
{-# INLINE sum #-}
sum = G.sum

-- | /O(n)/ Compute the product of the elements
product :: Vector (Rec Identity rs) -> (a, b)
{-# INLINE product #-}
product = G.product
-}

-- | /O(n)/ Yield the maximum element of the vector. The vector may not be
-- empty.
maximum :: (G.Vector Vector (Rec Identity rs), Ord (Rec Identity rs))
  => Vector (Rec Identity rs) -> Rec Identity rs
{-# INLINE maximum #-}
maximum = G.maximum

-- | /O(n)/ Yield the maximum element of the vector according to the given
-- comparison function. The vector may not be empty.
maximumBy :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Rec Identity rs -> Ordering) -> Vector (Rec Identity rs) -> Rec Identity rs
{-# INLINE maximumBy #-}
maximumBy = G.maximumBy

-- | /O(n)/ Yield the minimum element of the vector. The vector may not be
-- empty.
minimum :: (G.Vector Vector (Rec Identity rs), Ord (Rec Identity rs))
  => Vector (Rec Identity rs) -> Rec Identity rs
{-# INLINE minimum #-}
minimum = G.minimum

-- | /O(n)/ Yield the minimum element of the vector according to the given
-- comparison function. The vector may not be empty.
minimumBy :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Rec Identity rs -> Ordering) -> Vector (Rec Identity rs) -> Rec Identity rs
{-# INLINE minimumBy #-}
minimumBy = G.minimumBy

-- | /O(n)/ Yield the index of the maximum element of the vector. The vector
-- may not be empty.
maxIndex :: (G.Vector Vector (Rec Identity rs), Ord (Rec Identity rs))
  => Vector (Rec Identity rs) -> Int
{-# INLINE maxIndex #-}
maxIndex = G.maxIndex

-- | /O(n)/ Yield the index of the maximum element of the vector according to
-- the given comparison function. The vector may not be empty.
maxIndexBy :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Rec Identity rs -> Ordering) -> Vector (Rec Identity rs) -> Int
{-# INLINE maxIndexBy #-}
maxIndexBy = G.maxIndexBy

-- | /O(n)/ Yield the index of the minimum element of the vector. The vector
-- may not be empty.
minIndex :: (G.Vector Vector (Rec Identity rs), Ord (Rec Identity rs))
  => Vector (Rec Identity rs) -> Int
{-# INLINE minIndex #-}
minIndex = G.minIndex

-- | /O(n)/ Yield the index of the minimum element of the vector according to
-- the given comparison function. The vector may not be empty.
minIndexBy :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Rec Identity rs -> Ordering) -> Vector (Rec Identity rs) -> Int
{-# INLINE minIndexBy #-}
minIndexBy = G.minIndexBy

-- Monadic folds
-- -------------

-- | /O(n)/ Monadic fold
foldM :: (Monad m, G.Vector Vector (Rec Identity rs))
  => (r -> Rec Identity rs -> m r) -> r -> Vector (Rec Identity rs) -> m r
foldM = G.foldM
{-# INLINE foldM #-}

-- | /O(n)/ Monadic fold over non-empty vectors
fold1M :: (Monad m, G.Vector Vector (Rec Identity rs))
  => (Rec Identity rs -> Rec Identity rs -> m (Rec Identity rs)) -> Vector (Rec Identity rs) -> m (Rec Identity rs)
{-# INLINE fold1M #-}
fold1M = G.fold1M

-- | /O(n)/ Monadic fold with strict accumulator
foldM' :: (Monad m, G.Vector Vector (Rec Identity rs))
  => (r -> Rec Identity rs -> m r) -> r -> Vector (Rec Identity rs) -> m r
{-# INLINE foldM' #-}
foldM' = G.foldM'

-- | /O(n)/ Monadic fold over non-empty vectors with strict accumulator
fold1M' :: (Monad m, G.Vector Vector (Rec Identity rs))
  => (Rec Identity rs -> Rec Identity rs -> m (Rec Identity rs)) -> Vector (Rec Identity rs) -> m (Rec Identity rs)
{-# INLINE fold1M' #-}
fold1M' = G.fold1M'

-- | /O(n)/ Monadic fold that discards the result
foldM_ :: (Monad m, G.Vector Vector (Rec Identity rs))
  => (r -> Rec Identity rs -> m r) -> r -> Vector (Rec Identity rs) -> m ()
{-# INLINE foldM_ #-}
foldM_ = G.foldM_

-- | /O(n)/ Monadic fold over non-empty vectors that discards the result
fold1M_ :: (Monad m, G.Vector Vector (Rec Identity rs))
  => (Rec Identity rs -> Rec Identity rs -> m (Rec Identity rs)) -> Vector (Rec Identity rs) -> m ()
{-# INLINE fold1M_ #-}
fold1M_ = G.fold1M_

-- | /O(n)/ Monadic fold with strict accumulator that discards the result
foldM'_ :: (Monad m, G.Vector Vector (Rec Identity rs))
  => (r -> Rec Identity rs -> m r) -> r -> Vector (Rec Identity rs) -> m ()
{-# INLINE foldM'_ #-}
foldM'_ = G.foldM'_

-- | /O(n)/ Monadic fold over non-empty vectors with strict accumulator
-- that discards the result
fold1M'_ :: (Monad m, G.Vector Vector (Rec Identity rs))
  => (Rec Identity rs -> Rec Identity rs -> m (Rec Identity rs)) -> Vector (Rec Identity rs) -> m ()
{-# INLINE fold1M'_ #-}
fold1M'_ = G.fold1M'_


-- Prefix sums (scans)
-- -------------------

-- | /O(n)/ Prescan
--
-- @
-- prescanl f z = 'init' . 'scanl' f z
-- @
--
-- Example: @prescanl (+) 0 \<1,2,3,4\> = \<0,1,3,6\>@
--
prescanl :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> Rec Identity ss -> Rec Identity rs) -> Rec Identity rs -> Vector (Rec Identity ss) -> Vector (Rec Identity rs)
prescanl = G.prescanl
{-# INLINE prescanl #-}

-- | /O(n)/ Prescan with strict accumulator
prescanl' :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> Rec Identity ss -> Rec Identity rs) -> Rec Identity rs -> Vector (Rec Identity ss) -> Vector (Rec Identity rs)
prescanl' = G.prescanl'
{-# INLINE prescanl' #-}

-- | /O(n)/ Scan
--
-- @
-- postscanl f z = 'tail' . 'scanl' f z
-- @
--
-- Example: @postscanl (+) 0 \<1,2,3,4\> = \<1,3,6,10\>@
--
postscanl :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> Rec Identity ss -> Rec Identity rs) -> Rec Identity rs -> Vector (Rec Identity ss) -> Vector (Rec Identity rs)
postscanl = G.postscanl
{-# INLINE postscanl #-}

-- | /O(n)/ Scan with strict accumulator
postscanl' :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> Rec Identity ss -> Rec Identity rs) -> Rec Identity rs -> Vector (Rec Identity ss) -> Vector (Rec Identity rs)
postscanl' = G.postscanl'
{-# INLINE postscanl' #-}

-- | /O(n)/ Haskell-style scan
--
-- > scanl f z <x1,...,xn> = <y1,...,y(n+1)>
-- >   where y1 = z
-- >         yi = f y(i-1) x(i-1)
--
-- Example: @scanl (+) 0 \<1,2,3,4\> = \<0,1,3,6,10\>@
--
scanl :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> Rec Identity ss -> Rec Identity rs) -> Rec Identity rs -> Vector (Rec Identity ss) -> Vector (Rec Identity rs)
scanl = G.scanl
{-# INLINE scanl #-}

-- | /O(n)/ Haskell-style scan with strict accumulator
scanl' :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> Rec Identity ss -> Rec Identity rs) -> Rec Identity rs -> Vector (Rec Identity ss) -> Vector (Rec Identity rs)
scanl' = G.scanl'
{-# INLINE scanl' #-}

-- | /O(n)/ Scan over a non-empty vector
--
-- > scanl f <x1,...,xn> = <y1,...,yn>
-- >   where y1 = x1
-- >         yi = f y(i-1) xi
--
scanl1 :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Rec Identity rs -> Rec Identity rs) -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
scanl1 = G.scanl1
{-# INLINE scanl1 #-}

-- | /O(n)/ Scan over a non-empty vector with a strict accumulator
scanl1' :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Rec Identity rs -> Rec Identity rs) -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
scanl1' = G.scanl1'
{-# INLINE scanl1' #-}

-- | /O(n)/ Right-to-left prescan
--
-- @
-- prescanr f z = 'reverse' . 'prescanl' (flip f) z . 'reverse'
-- @
--
prescanr :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> Rec Identity ss -> Rec Identity ss) -> Rec Identity ss -> Vector (Rec Identity rs) -> Vector (Rec Identity ss)
{-# INLINE prescanr #-}
prescanr = G.prescanr

-- | /O(n)/ Right-to-left prescan with strict accumulator
prescanr' :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> Rec Identity ss -> Rec Identity ss) -> Rec Identity ss -> Vector (Rec Identity rs) -> Vector (Rec Identity ss)
prescanr' = G.prescanr'
{-# INLINE prescanr' #-}

-- | /O(n)/ Right-to-left scan
postscanr :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> Rec Identity ss -> Rec Identity ss) -> Rec Identity ss -> Vector (Rec Identity rs) -> Vector (Rec Identity ss)
postscanr = G.postscanr
{-# INLINE postscanr #-}

-- | /O(n)/ Right-to-left scan with strict accumulator
postscanr' :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> Rec Identity ss -> Rec Identity ss) -> Rec Identity ss -> Vector (Rec Identity rs) -> Vector (Rec Identity ss)
postscanr' = G.postscanr'
{-# INLINE postscanr' #-}

-- | /O(n)/ Right-to-left Haskell-style scan
scanr :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> Rec Identity ss -> Rec Identity ss) -> Rec Identity ss -> Vector (Rec Identity rs) -> Vector (Rec Identity ss)
scanr = G.scanr
{-# INLINE scanr #-}

-- | /O(n)/ Right-to-left Haskell-style scan with strict accumulator
scanr' :: (G.Vector Vector (Rec Identity rs), G.Vector Vector (Rec Identity ss))
  => (Rec Identity rs -> Rec Identity ss -> Rec Identity ss) -> Rec Identity ss -> Vector (Rec Identity rs) -> Vector (Rec Identity ss)
scanr' = G.scanr'
{-# INLINE scanr' #-}

-- | /O(n)/ Right-to-left scan over a non-empty vector
scanr1 :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Rec Identity rs -> Rec Identity rs) -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
{-# INLINE scanr1 #-}
scanr1 = G.scanr1

-- | /O(n)/ Right-to-left scan over a non-empty vector with a strict
-- accumulator
scanr1' :: G.Vector Vector (Rec Identity rs)
  => (Rec Identity rs -> Rec Identity rs -> Rec Identity rs) -> Vector (Rec Identity rs) -> Vector (Rec Identity rs)
{-# INLINE scanr1' #-}
scanr1' = G.scanr1'

-- | /O(n)/ Convert a vector to a list
toList :: G.Vector Vector (Rec Identity rs)
  => Vector (Rec Identity rs) -> [Rec Identity rs]
toList = G.toList
{-# INLINE toList #-}

-- | /O(n)/ Convert a list to a vector
fromList :: G.Vector Vector (Rec Identity rs)
  => [Rec Identity rs] -> Vector (Rec Identity rs)
fromList = G.fromList
{-# INLINE fromList #-}

-- | /O(n)/ Convert the first @n@ elements of a list to a vector
--
-- @
-- fromListN n xs = 'fromList' ('take' n xs)
-- @
fromListN :: G.Vector Vector (Rec Identity rs)
  => Int -> [Rec Identity rs] -> Vector (Rec Identity rs)
fromListN = G.fromListN
{-# INLINE fromListN #-}

-- Conversions - Mutable vectors
-- -----------------------------

-- | /O(1)/ Unsafe convert a mutable vector to an immutable one without
-- copying. The mutable vector may not be used after this operation.
unsafeFreeze :: (PrimMonad m, G.Vector Vector (Rec Identity rs))
             => G.Mutable Vector (PrimState m) (Rec Identity rs) -> m (Vector (Rec Identity rs))
unsafeFreeze = G.unsafeFreeze
{-# INLINE unsafeFreeze #-}

-- | /O(1)/ Unsafely convert an immutable vector to a mutable one without
-- copying. The immutable vector may not be used after this operation.
unsafeThaw :: (PrimMonad m, G.Vector Vector (Rec Identity rs))
           => Vector (Rec Identity rs) -> m (G.Mutable Vector (PrimState m) (Rec Identity rs))
unsafeThaw = G.unsafeThaw
{-# INLINE unsafeThaw #-}

-- | /O(n)/ Yield a mutable copy of the immutable vector.
thaw :: (PrimMonad m, G.Vector Vector (Rec Identity rs))
     => Vector (Rec Identity rs) -> m (G.Mutable Vector (PrimState m) (Rec Identity rs))
thaw = G.thaw
{-# INLINE thaw #-}

-- | /O(n)/ Yield an immutable copy of the mutable vector.
freeze :: (PrimMonad m, G.Vector Vector (Rec Identity rs))
       => G.Mutable Vector (PrimState m) (Rec Identity rs) -> m (Vector (Rec Identity rs))
freeze = G.freeze
{-# INLINE freeze #-}

-- | /O(n)/ Copy an immutable vector into a mutable one. The two vectors must
-- have the same length. This is not checked.
unsafeCopy :: (PrimMonad m, G.Vector Vector (Rec Identity rs))
           => G.Mutable Vector (PrimState m) (Rec Identity rs) -> Vector (Rec Identity rs) -> m ()
unsafeCopy = G.unsafeCopy
{-# INLINE unsafeCopy #-}

-- | /O(n)/ Copy an immutable vector into a mutable one. The two vectors must
-- have the same length.
copy :: (PrimMonad m, G.Vector Vector (Rec Identity rs))
     => G.Mutable Vector (PrimState m) (Rec Identity rs) -> Vector (Rec Identity rs) -> m ()
copy = G.copy
{-# INLINE copy #-}


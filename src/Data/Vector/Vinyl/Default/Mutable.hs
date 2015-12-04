{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

-- |
-- Module      : Data.Vector.Vinyl.Default.Mutable
-- Copyright   : Andrew Martin
-- License     : BSD-style
--
-- Maintainer  : Andrew Martin <andrew.thaddeus@gmail.com>
-- Stability   : experimental
-- Portability : non-portable
--
-- Vectors for vinyl records
--

module Data.Vector.Vinyl.Default.Mutable (
  -- * Mutable vectors of primitive types
  MVector(..), 

  -- * Accessors

  -- ** Length information
  length, null,

  -- ** Extracting subvectors
  slice, init, tail, take, drop, splitAt,
  unsafeSlice, unsafeInit, unsafeTail, unsafeTake, unsafeDrop,

  -- ** Overlapping
  overlaps,

  -- * Construction

  -- ** Initialisation
  new, unsafeNew, replicate, replicateM, clone,

  -- ** Growing
  grow, unsafeGrow,

  -- ** Restricting memory usage
  clear,

  -- * Zipping and unzipping - Omitting for now

  -- * Accessing individual elements
  read, write, swap,
  unsafeRead, unsafeWrite, unsafeSwap,

  -- * Modifying vectors

  -- ** Filling and copying
  set, copy, move, unsafeCopy, unsafeMove
) where

import Data.Vector.Vinyl.Default.Internal
import qualified Data.Vector.Generic.Mutable as G
import Data.Vector.Fusion.Util ( delayed_min )
import Control.Monad.Primitive
import Data.Vinyl.Core (Rec)
import Data.Vinyl.Functor (Identity)

import Prelude hiding ( length, null, replicate, reverse, map, read,
                        take, drop, splitAt, init, tail,
                        zip, zip3, unzip, unzip3 )

-- Length information
-- ------------------

-- | Length of the mutable vector.
length :: MVector s (Rec Identity rs) -> Int
{-# INLINE length #-}
length (MV i _) = i

-- | Check whether the vector is empty
null :: MVector s (Rec Identity rs) -> Bool
{-# INLINE null #-}
null (MV i _) = i == 0

-- Extracting subvectors
-- ---------------------

-- | Yield a part of the mutable vector without copying it.
slice :: G.MVector MVector (Rec Identity rs) => Int -> Int -> MVector s (Rec Identity rs) -> MVector s (Rec Identity rs)
{-# INLINE slice #-}
slice = G.slice

take :: G.MVector MVector (Rec Identity rs) => Int -> MVector s (Rec Identity rs) -> MVector s (Rec Identity rs)
{-# INLINE take #-}
take = G.take

drop :: G.MVector MVector (Rec Identity rs) => Int -> MVector s (Rec Identity rs) -> MVector s (Rec Identity rs)
{-# INLINE drop #-}
drop = G.drop

splitAt :: G.MVector MVector (Rec Identity rs) => Int -> MVector s (Rec Identity rs) -> (MVector s (Rec Identity rs), MVector s (Rec Identity rs))
{-# INLINE splitAt #-}
splitAt = G.splitAt

init :: G.MVector MVector (Rec Identity rs) => MVector s (Rec Identity rs) -> MVector s (Rec Identity rs)
{-# INLINE init #-}
init = G.init

tail :: G.MVector MVector (Rec Identity rs) => MVector s (Rec Identity rs) -> MVector s (Rec Identity rs)
{-# INLINE tail #-}
tail = G.tail

-- | Yield a part of the mutable vector without copying it. No bounds checks
-- are performed.
unsafeSlice :: G.MVector MVector (Rec Identity rs)
            => Int  -- ^ starting index
            -> Int  -- ^ length of the slice
            -> MVector s (Rec Identity rs)
            -> MVector s (Rec Identity rs)
{-# INLINE unsafeSlice #-}
unsafeSlice = G.unsafeSlice

unsafeTake :: G.MVector MVector (Rec Identity rs) => Int -> MVector s (Rec Identity rs) -> MVector s (Rec Identity rs)
{-# INLINE unsafeTake #-}
unsafeTake = G.unsafeTake

unsafeDrop :: G.MVector MVector (Rec Identity rs) => Int -> MVector s (Rec Identity rs) -> MVector s (Rec Identity rs)
{-# INLINE unsafeDrop #-}
unsafeDrop = G.unsafeDrop

unsafeInit :: G.MVector MVector (Rec Identity rs) => MVector s (Rec Identity rs) -> MVector s (Rec Identity rs)
{-# INLINE unsafeInit #-}
unsafeInit = G.unsafeInit

unsafeTail :: G.MVector MVector (Rec Identity rs) => MVector s (Rec Identity rs) -> MVector s (Rec Identity rs)
{-# INLINE unsafeTail #-}
unsafeTail = G.unsafeTail

-- Overlapping
-- -----------

-- | Check whether two vectors overlap.
overlaps :: G.MVector MVector (Rec Identity rs) => MVector s (Rec Identity rs) -> MVector s (Rec Identity rs) -> Bool
{-# INLINE overlaps #-}
overlaps = G.overlaps

-- Initialisation
-- --------------

-- | Create a mutable vector of the given length.
new :: (PrimMonad m, G.MVector MVector (Rec Identity rs)) => Int -> m (MVector (PrimState m) (Rec Identity rs))
{-# INLINE new #-}
new = G.new

-- | Create a mutable vector of the given length. The length is not checked.
unsafeNew :: (PrimMonad m, G.MVector MVector (Rec Identity rs)) => Int -> m (MVector (PrimState m) (Rec Identity rs))
{-# INLINE unsafeNew #-}
unsafeNew = G.unsafeNew

-- | Create a mutable vector of the given length (0 if the length is negative)
-- and fill it with an initial value.
replicate :: (PrimMonad m, G.MVector MVector (Rec Identity rs)) => Int -> (Rec Identity rs) -> m (MVector (PrimState m) (Rec Identity rs))
{-# INLINE replicate #-}
replicate = G.replicate

-- | Create a mutable vector of the given length (0 if the length is negative)
-- and fill it with values produced by repeatedly executing the monadic action.
replicateM :: (PrimMonad m, G.MVector MVector (Rec Identity rs)) => Int -> m (Rec Identity rs) -> m (MVector (PrimState m) (Rec Identity rs))
{-# INLINE replicateM #-}
replicateM = G.replicateM

-- | Create a copy of a mutable vector.
clone :: (PrimMonad m, G.MVector MVector (Rec Identity rs))
      => MVector (PrimState m) (Rec Identity rs) -> m (MVector (PrimState m) (Rec Identity rs))
{-# INLINE clone #-}
clone = G.clone

-- Growing
-- -------

-- | Grow a vector by the given number of elements. The number must be
-- positive.
grow :: (PrimMonad m, G.MVector MVector (Rec Identity rs))
              => MVector (PrimState m) (Rec Identity rs) -> Int -> m (MVector (PrimState m) (Rec Identity rs))
{-# INLINE grow #-}
grow = G.grow

-- | Grow a vector by the given number of elements. The number must be
-- positive but this is not checked.
unsafeGrow :: (PrimMonad m, G.MVector MVector (Rec Identity rs))
               => MVector (PrimState m) (Rec Identity rs) -> Int -> m (MVector (PrimState m) (Rec Identity rs))
{-# INLINE unsafeGrow #-}
unsafeGrow = G.unsafeGrow

-- Restricting memory usage
-- ------------------------

-- | Reset all elements of the vector to some undefined value, clearing all
-- references to external objects. This is usually a noop for unboxed vectors.
clear :: (PrimMonad m, G.MVector MVector (Rec Identity rs)) => MVector (PrimState m) (Rec Identity rs) -> m ()
{-# INLINE clear #-}
clear = G.clear

-- Accessing individual elements
-- -----------------------------

-- | Yield the element at the given position.
read :: (PrimMonad m, G.MVector MVector (Rec Identity rs)) => MVector (PrimState m) (Rec Identity rs) -> Int -> m (Rec Identity rs)
{-# INLINE read #-}
read = G.read

-- | Replace the element at the given position.
write :: (PrimMonad m, G.MVector MVector (Rec Identity rs)) => MVector (PrimState m) (Rec Identity rs) -> Int -> (Rec Identity rs) -> m ()
{-# INLINE write #-}
write = G.write

-- | Swap the elements at the given positions.
swap :: (PrimMonad m, G.MVector MVector (Rec Identity rs)) => MVector (PrimState m) (Rec Identity rs) -> Int -> Int -> m ()
{-# INLINE swap #-}
swap = G.swap


-- | Yield the element at the given position. No bounds checks are performed.
unsafeRead :: (PrimMonad m, G.MVector MVector (Rec Identity rs)) => MVector (PrimState m) (Rec Identity rs) -> Int -> m (Rec Identity rs)
{-# INLINE unsafeRead #-}
unsafeRead = G.unsafeRead

-- | Replace the element at the given position. No bounds checks are performed.
unsafeWrite
    :: (PrimMonad m, G.MVector MVector (Rec Identity rs)) =>  MVector (PrimState m) (Rec Identity rs) -> Int -> (Rec Identity rs) -> m ()
{-# INLINE unsafeWrite #-}
unsafeWrite = G.unsafeWrite

-- | Swap the elements at the given positions. No bounds checks are performed.
unsafeSwap
    :: (PrimMonad m, G.MVector MVector (Rec Identity rs)) => MVector (PrimState m) (Rec Identity rs) -> Int -> Int -> m ()
{-# INLINE unsafeSwap #-}
unsafeSwap = G.unsafeSwap

-- Filling and copying
-- -------------------

-- | Set all elements of the vector to the given value.
set :: (PrimMonad m, G.MVector MVector (Rec Identity rs)) => MVector (PrimState m) (Rec Identity rs) -> (Rec Identity rs) -> m ()
{-# INLINE set #-}
set = G.set

-- | Copy a vector. The two vectors must have the same length and may not
-- overlap.
copy :: (PrimMonad m, G.MVector MVector (Rec Identity rs))
                 => MVector (PrimState m) (Rec Identity rs) -> MVector (PrimState m) (Rec Identity rs) -> m ()
{-# INLINE copy #-}
copy = G.copy

-- | Copy a vector. The two vectors must have the same length and may not
-- overlap. This is not checked.
unsafeCopy :: (PrimMonad m, G.MVector MVector (Rec Identity rs))
           => MVector (PrimState m) (Rec Identity rs)   -- ^ target
           -> MVector (PrimState m) (Rec Identity rs)   -- ^ source
           -> m ()
{-# INLINE unsafeCopy #-}
unsafeCopy = G.unsafeCopy

-- | Move the contents of a vector. The two vectors must have the same
-- length.
--
-- If the vectors do not overlap, then this is equivalent to 'copy'.
-- Otherwise, the copying is performed as if the source vector were
-- copied to a temporary vector and then the temporary vector was copied
-- to the target vector.
move :: (PrimMonad m, G.MVector MVector (Rec Identity rs))
     => MVector (PrimState m) (Rec Identity rs) -> MVector (PrimState m) (Rec Identity rs) -> m ()
{-# INLINE move #-}
move = G.move

-- | Move the contents of a vector. The two vectors must have the same
-- length, but this is not checked.
--
-- If the vectors do not overlap, then this is equivalent to 'unsafeCopy'.
-- Otherwise, the copying is performed as if the source vector were
-- copied to a temporary vector and then the temporary vector was copied
-- to the target vector.
unsafeMove :: (PrimMonad m, G.MVector MVector (Rec Identity rs))
           => MVector (PrimState m) (Rec Identity rs)   -- ^ target
           -> MVector (PrimState m) (Rec Identity rs)   -- ^ source
           -> m ()
{-# INLINE unsafeMove #-}
unsafeMove = G.unsafeMove


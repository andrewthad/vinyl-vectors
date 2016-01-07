{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}

#ifndef MIN_VERSION_vector
#define MIN_VERSION_vector(x,y,z) 1
#endif

module Data.Vector.Vec.Internal
  ( MVector(..)
  , Vector(..)
  ) where

-- This is not yet reflected in the naming of this module, but this is only
-- good for non-empty vecs.

import Control.Monad
import Data.Monoid
import Data.Typeable (Typeable)
import GHC.Exts (Constraint)
import Control.Monad.Primitive (PrimMonad,PrimState)
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Generic as G

#if MIN_VERSION_vector(0,11,0)
import Data.Vector.Fusion.Bundle as Stream
#else
import Data.Vector.Fusion.Stream as Stream
#endif

import Prelude hiding ( length, null, replicate, reverse, map, read, take, drop, init, tail )
import Text.Read
import Data.List.TypeLevel (Nat(..),Natty(..),HasNatty(..))
import Data.Vec (Vec(VecNil,VecCons),vcopies)
import Data.Foldable (traverse_, sequenceA_)

data MVector :: (* -> * -> *) -> * -> * -> * where
  MV :: !(Vec n (v s a)) -> MVector v s (Vec n a)
  deriving Typeable

data Vector :: (* -> *) -> * -> * where
  V :: !(Vec n (v a)) -> Vector v (Vec n a)
  deriving Typeable

type instance G.Mutable (Vector v) = MVector (G.Mutable v)

instance (GM.MVector v a, HasNatty n) => GM.MVector (MVector v) (Vec ('Succ n) a) where
  basicLength (MV (VecCons v _)) = GM.basicLength v
  {-# INLINE basicLength #-}
  
  basicUnsafeSlice s e (MV v) = MV (fmap (GM.basicUnsafeSlice s e) v)
  {-# INLINE basicUnsafeSlice #-}

  basicOverlaps (MV a) (MV b) = basicOverlaps' a b
  {-# INLINE basicOverlaps #-}

  basicUnsafeNew n = fmap MV 
    (traverse (const $ GM.basicUnsafeNew n) (vcopies (natty :: Natty ('Succ n)) ()))
  {-# INLINE basicUnsafeNew #-}

  basicUnsafeReplicate n a = fmap MV (traverse (GM.basicUnsafeReplicate n) a)
  {-# INLINE basicUnsafeReplicate #-}

  basicUnsafeRead (MV v) n = traverse (flip GM.basicUnsafeRead n) v
  {-# INLINE basicUnsafeRead #-}

  basicUnsafeWrite (MV v) n a = sequenceA_ (write <$> v <*> a)
    where write vector val = GM.basicUnsafeWrite vector n val
  {-# INLINE basicUnsafeWrite #-}

  basicClear (MV v) = traverse_ GM.basicClear v
  {-# INLINE basicClear #-}

  basicSet (MV v) a = sequenceA_ (GM.basicSet <$> v <*> a)
  {-# INLINE basicSet #-}

  basicUnsafeCopy (MV a) (MV b) = sequenceA_ (GM.basicUnsafeCopy <$> a <*> b)
  {-# INLINE basicUnsafeCopy #-}

  basicUnsafeMove (MV a) (MV b) = sequenceA_ (GM.basicUnsafeMove <$> a <*> b)
  {-# INLINE basicUnsafeMove #-}

  basicUnsafeGrow (MV v) i = fmap MV (traverse (flip GM.basicUnsafeGrow i) v)
  {-# INLINE basicUnsafeGrow #-}

#if MIN_VERSION_vector(0,11,0)
  basicInitialize (MV v) = traverse_ GM.basicInitialize v
  {-# INLINE basicInitialize #-}
#endif

instance (G.Vector v a, HasNatty n) => G.Vector (Vector v) (Vec ('Succ n) a) where
  basicUnsafeFreeze (MV v) = fmap V (traverse G.basicUnsafeFreeze v)
  {-# INLINE basicUnsafeFreeze #-}

  basicUnsafeThaw (V v) = fmap MV (traverse G.basicUnsafeThaw v)
  {-# INLINE basicUnsafeThaw #-}

  basicLength (V (VecCons v _)) = G.basicLength v
  {-# INLINE basicLength #-}

  basicUnsafeSlice s e (V v) = V (fmap (G.basicUnsafeSlice s e) v)
  {-# INLINE basicUnsafeSlice #-}

  basicUnsafeIndexM (V v) n = traverse (flip G.basicUnsafeIndexM n) v
  {-# INLINE basicUnsafeIndexM #-}

  basicUnsafeCopy (MV mv) (V v) = sequence_ (G.basicUnsafeCopy <$> mv <*> v)
  {-# INLINE basicUnsafeCopy #-}

  elemseq (V v) a b = elemseq' v a b
  {-# INLINE elemseq #-}

basicOverlaps' :: GM.MVector v a => Vec n (v s a) -> Vec n (v s a) -> Bool
basicOverlaps' VecNil VecNil = False
basicOverlaps' (VecCons a anext) (VecCons b bnext) = GM.basicOverlaps a b || basicOverlaps' anext bnext

elemseq' :: G.Vector v a => Vec n (v a) -> Vec n a -> b -> b
elemseq' VecNil VecNil b = b
elemseq' (VecCons v vnext) (VecCons a anext) b = G.elemseq v a (elemseq' vnext anext b)


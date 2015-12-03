{-# LANGUAGE CPP #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE InstanceSigs #-}

#ifndef MIN_VERSION_vector
#define MIN_VERSION_vector(x,y,z) 1
#endif

module Data.Vector.Vinyl.Internal
  ( MVector(..)
  , Vector(..)
  ) where

import Control.Monad
import Data.Monoid
import Data.Typeable (Typeable)
import GHC.Exts (Constraint)
import Control.Monad.Primitive (PrimMonad,PrimState)
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Generic as G
import qualified Data.Vector as B
import qualified Data.Vector.Unboxed as U

#if MIN_VERSION_vector(0,11,0)
import Data.Vector.Fusion.Bundle as Stream
#else
import Data.Vector.Fusion.Stream as Stream
#endif

import Prelude hiding ( length, null, replicate, reverse, map, read, take, drop, init, tail )
import Text.Read
import Data.Proxy

import Data.Vinyl.Core(Rec(..))
import Data.Vinyl.Functor (Identity(..))

class ( GM.MVector (G.Mutable (Vectorize t)) t
      , G.Vector (Vectorize t) t
      ) => CanVectorize t where
  type Vectorize t :: * -> *

-- | A constraint on each element of a type-level list.
type family LAll c ts :: Constraint where
  LAll c '[] = ()
  LAll c (t ': ts) = (c t, LAll c ts)

-- | The most efficient vector type for each column data type.
instance CanVectorize Int where
  type Vectorize Int = U.Vector
instance CanVectorize Bool where
  type Vectorize Bool = U.Vector
instance CanVectorize Float where
  type Vectorize Float = U.Vector
instance CanVectorize Double where
  type Vectorize Double = U.Vector

newtype VectorMVal s t = VectorMVal { getVectorMVal :: G.Mutable (Vectorize t) s t }

data MVector :: * -> * -> * where
  MV :: !Int -> !(Rec (VectorMVal s) rs) -> MVector s (Rec Identity rs)
  deriving Typeable

type family Tail rs where
  Tail (r ': rs) = rs

-- data MVector :: (* -> * -> *) -> (* -> * -> *) -> * -> * -> * where
--   MV :: !(u s a) -> !(v s b) -> MVector u v s (a, b)

instance ( GM.MVector MVector (Rec Identity rs)
         , CanVectorize r
         )
    => GM.MVector MVector (Rec Identity (r ': rs)) where
  basicLength (MV i _) = i
  {-# INLINE basicLength #-}

  basicUnsafeSlice s e (MV i (VectorMVal v :& rs)) = case GM.basicUnsafeSlice s e (MV i rs) of
    MV _ rsNext -> MV e (VectorMVal (GM.basicUnsafeSlice s e v) :& rsNext)
  {-# INLINE basicUnsafeSlice #-}

  basicOverlaps (MV i (VectorMVal a :& as)) (MV j (VectorMVal b :& bs)) = 
    GM.basicOverlaps a b || GM.basicOverlaps (MV i as) (MV j bs)
  {-# INLINE basicOverlaps #-}

  basicUnsafeNew :: forall m. PrimMonad m => Int -> m (MVector (PrimState m) (Rec Identity (r ': rs)))
  basicUnsafeNew n = do
    r <- GM.basicUnsafeNew n
    m <- GM.basicUnsafeNew n
    return (MV n (VectorMVal r :& go m))
    where 
      go :: MVector (PrimState m) (Rec Identity rs) -> Rec (VectorMVal (PrimState m)) rs
      go (MV _ rs) = rs
  {-# INLINE basicUnsafeNew #-}

-- instance (GM.MVector u a, GM.MVector v b) => GM.MVector (MVector u v) (a, b) where
--   basicUnsafeNew n = liftM2 MV (GM.basicUnsafeNew n) (GM.basicUnsafeNew n)
--   {-# INLINE basicUnsafeNew #-}
--   basicUnsafeReplicate n (k,v) = liftM2 MV (GM.basicUnsafeReplicate n k) (GM.basicUnsafeReplicate n v)
--   {-# INLINE basicUnsafeReplicate #-}
--   basicUnsafeRead (MV ks vs) n = liftM2 (,) (GM.basicUnsafeRead ks n) (GM.basicUnsafeRead vs n)
--   {-# INLINE basicUnsafeRead #-}
--   basicUnsafeWrite (MV ks vs) n (k,v) = do
--     GM.basicUnsafeWrite ks n k
--     GM.basicUnsafeWrite vs n v
--   {-# INLINE basicUnsafeWrite #-}
--   basicClear (MV ks vs) = do
--     GM.basicClear ks
--     GM.basicClear vs
--   {-# INLINE basicClear #-}
--   basicSet (MV ks vs) (k,v) = do
--     GM.basicSet ks k
--     GM.basicSet vs v
--   {-# INLINE basicSet #-}
--   basicUnsafeCopy (MV ks vs) (MV ks' vs') = do
--     GM.basicUnsafeCopy ks ks'
--     GM.basicUnsafeCopy vs vs'
--   {-# INLINE basicUnsafeCopy #-}
--   basicUnsafeMove (MV ks vs) (MV ks' vs') = do
--     GM.basicUnsafeMove ks ks'
--     GM.basicUnsafeMove vs vs'
--   {-# INLINE basicUnsafeMove #-}
--   basicUnsafeGrow (MV ks vs) n = liftM2 MV (GM.basicUnsafeGrow ks n) (GM.basicUnsafeGrow vs n)
--   {-# INLINE basicUnsafeGrow #-}
-- #if MIN_VERSION_vector(0,11,0)
--   basicInitialize (MV ks vs) = GM.basicInitialize ks >> GM.basicInitialize vs
--   {-# INLINE basicInitialize #-}
-- #endif
-- 
-- -- hybrid vectors
-- data Vector :: (* -> *) -> (* -> *) -> * -> * where
--   V :: !(u a) -> !(v b) -> Vector u v (a, b)
--   deriving Typeable
-- 
-- type instance G.Mutable (Vector u v) = MVector (G.Mutable u) (G.Mutable v)
-- 
-- instance (G.Vector u a, G.Vector v b) => G.Vector (Vector u v) (a, b) where
--   basicUnsafeFreeze (MV ks vs) = liftM2 V (G.basicUnsafeFreeze ks) (G.basicUnsafeFreeze vs)
--   {-# INLINE basicUnsafeFreeze #-}
--   basicUnsafeThaw (V ks vs) = liftM2 MV (G.basicUnsafeThaw ks) (G.basicUnsafeThaw vs)
--   {-# INLINE basicUnsafeThaw #-}
--   basicLength (V ks _) = G.basicLength ks
--   {-# INLINE basicLength #-}
--   basicUnsafeSlice i j (V ks vs) = V (G.basicUnsafeSlice i j ks) (G.basicUnsafeSlice i j vs)
--   {-# INLINE basicUnsafeSlice #-}
--   basicUnsafeIndexM (V ks vs) n = liftM2 (,) (G.basicUnsafeIndexM ks n) (G.basicUnsafeIndexM vs n)
--   {-# INLINE basicUnsafeIndexM #-}
--   basicUnsafeCopy (MV ks vs) (V ks' vs') = do
--     G.basicUnsafeCopy ks ks'
--     G.basicUnsafeCopy vs vs'
--   {-# INLINE basicUnsafeCopy #-}
--   elemseq (V ks vs) (k,v) b = G.elemseq ks k (G.elemseq vs v b)
--   {-# INLINE elemseq #-}
-- 
-- instance (G.Vector u a, G.Vector v b, c ~ (a, b)) => Monoid (Vector u v c) where
--   mappend = (G.++)
--   {-# INLINE mappend #-}
--   mempty = G.empty
--   {-# INLINE mempty #-}
--   mconcat = G.concat
--   {-# INLINE mconcat #-}
-- 
-- instance (G.Vector u a, G.Vector v b, Show a, Show b, c ~ (a, b)) => Show (Vector u v c) where
--   showsPrec = G.showsPrec
-- 
-- instance (G.Vector u a, G.Vector v b, Read a, Read b, c ~ (a, b)) => Read (Vector u v c) where
--   readPrec = G.readPrec
--   readListPrec = readListPrecDefault
-- 
-- instance (G.Vector u a, G.Vector v b, Eq a, Eq b, c ~ (a, b)) => Eq (Vector u v c) where
--   xs == ys = Stream.eq (G.stream xs) (G.stream ys)
--   {-# INLINE (==) #-}
-- 
--   xs /= ys = not (Stream.eq (G.stream xs) (G.stream ys))
--   {-# INLINE (/=) #-}
-- 
-- instance (G.Vector u a, G.Vector v b, Ord a, Ord b, c ~ (a, b)) => Ord (Vector u v c) where
--   {-# INLINE compare #-}
--   compare xs ys = Stream.cmp (G.stream xs) (G.stream ys)
-- 
--   {-# INLINE (<) #-}
--   xs < ys = Stream.cmp (G.stream xs) (G.stream ys) == LT
-- 
--   {-# INLINE (<=) #-}
--   xs <= ys = Stream.cmp (G.stream xs) (G.stream ys) /= GT
-- 
--   {-# INLINE (>) #-}
--   xs > ys = Stream.cmp (G.stream xs) (G.stream ys) == GT
-- 
--   {-# INLINE (>=) #-}
--   xs >= ys = Stream.cmp (G.stream xs) (G.stream ys) /= LT
-- 

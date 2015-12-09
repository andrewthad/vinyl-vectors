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

module Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Internal
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
import Data.Vector.Vinyl.Default.Types (VectorVal(..),MVectorVal(..),HasDefaultVector(..))

data MVector :: * -> * -> * where
  MV :: !(Rec (MVectorVal s) rs) -> MVector s (Rec Identity rs)
  deriving Typeable

instance ( HasDefaultVector r
         )
    => GM.MVector MVector (Rec Identity (r ': '[])) where
  basicLength (MV (MVectorVal v :& RNil)) = GM.basicLength v
  {-# INLINE basicLength #-}
  basicUnsafeSlice s e (MV (MVectorVal v :& RNil)) = MV (MVectorVal (GM.basicUnsafeSlice s e v) :& RNil)
  {-# INLINE basicUnsafeSlice #-}
  basicOverlaps (MV (MVectorVal a :& RNil)) (MV (MVectorVal b :& RNil)) = GM.basicOverlaps a b 
  {-# INLINE basicOverlaps #-}
  basicUnsafeNew n = do
    r <- GM.basicUnsafeNew n 
    return (MV (MVectorVal r :& RNil))
  {-# INLINE basicUnsafeNew #-}
  basicUnsafeReplicate n (Identity v :& RNil) = do
    r <- GM.basicUnsafeReplicate n v 
    return (MV (MVectorVal r :& RNil))
  {-# INLINE basicUnsafeReplicate #-}
  basicUnsafeRead (MV (MVectorVal v :& RNil)) n = do
    r <- GM.basicUnsafeRead v n
    return (Identity r :& RNil)
  {-# INLINE basicUnsafeRead #-}
  basicUnsafeWrite (MV (MVectorVal v :& RNil)) n (Identity r :& RNil) = GM.basicUnsafeWrite v n r
  {-# INLINE basicUnsafeWrite #-}
  basicClear (MV (MVectorVal v :& RNil)) = GM.basicClear v
  {-# INLINE basicClear #-}
  basicSet (MV (MVectorVal v :& RNil)) (Identity r :& RNil) = GM.basicSet v r
  {-# INLINE basicSet #-}
  basicUnsafeCopy (MV (MVectorVal a :& RNil)) (MV (MVectorVal b :& RNil)) = GM.basicUnsafeCopy a b
  {-# INLINE basicUnsafeCopy #-}
  basicUnsafeMove (MV (MVectorVal a :& RNil)) (MV (MVectorVal b :& RNil)) = GM.basicUnsafeMove a b
  {-# INLINE basicUnsafeMove #-}
  basicUnsafeGrow (MV (MVectorVal v :& RNil)) n = do
    r <- GM.basicUnsafeGrow v n
    return (MV (MVectorVal r :& RNil))
  {-# INLINE basicUnsafeGrow #-}
#if MIN_VERSION_vector(0,11,0)
  basicInitialize (MV (MVectorVal v :& RNil)) = do
    GM.basicInitialize v
  {-# INLINE basicInitialize #-}
#endif

instance ( GM.MVector MVector (Rec Identity (s ': rs))
         , HasDefaultVector r
         )
    => GM.MVector MVector (Rec Identity (r ': s ': rs)) where
  basicLength (MV (MVectorVal v :& _)) = GM.basicLength v
  {-# INLINE basicLength #-}

  basicUnsafeSlice s e (MV (MVectorVal v :& rs)) = case GM.basicUnsafeSlice s e (MV rs) of
    MV rsNext -> MV (MVectorVal (GM.basicUnsafeSlice s e v) :& rsNext)
  {-# INLINE basicUnsafeSlice #-}

  basicOverlaps (MV (MVectorVal a :& as)) (MV (MVectorVal b :& bs)) = 
    GM.basicOverlaps a b || GM.basicOverlaps (MV as) (MV bs)
  {-# INLINE basicOverlaps #-}

  basicUnsafeNew :: forall m. PrimMonad m => Int -> m (MVector (PrimState m) (Rec Identity (r ': s ': rs)))
  basicUnsafeNew n = 
    consVec (Proxy :: Proxy m) <$> GM.basicUnsafeNew n <*> GM.basicUnsafeNew n
  {-# INLINE basicUnsafeNew #-}
  
  basicUnsafeReplicate :: forall m. PrimMonad m => Int -> Rec Identity (r ': s ': rs) -> m (MVector (PrimState m) (Rec Identity (r ': s ': rs)))
  basicUnsafeReplicate n (Identity v :& rs) = 
    consVec (Proxy :: Proxy m) <$> GM.basicUnsafeReplicate n v <*> GM.basicUnsafeReplicate n rs
  {-# INLINE basicUnsafeReplicate #-}

  basicUnsafeRead (MV (MVectorVal v :& rs)) n = do
    r <- GM.basicUnsafeRead v n
    rs <- GM.basicUnsafeRead (MV rs) n
    return (Identity r :& rs)
  {-# INLINE basicUnsafeRead #-}

  basicUnsafeWrite (MV (MVectorVal v :& vrs)) n (Identity r :& rs) = do
    GM.basicUnsafeWrite v n r
    GM.basicUnsafeWrite (MV vrs) n rs
  {-# INLINE basicUnsafeWrite #-}

  basicClear (MV (MVectorVal v :& vrs)) = do
    GM.basicClear v
    GM.basicClear (MV vrs)
  {-# INLINE basicClear #-}

  basicSet (MV (MVectorVal v :& vrs)) (Identity r :& rs) = do
    GM.basicSet v r
    GM.basicSet (MV vrs) rs
  {-# INLINE basicSet #-}

  basicUnsafeCopy (MV (MVectorVal a :& as)) (MV (MVectorVal b :& bs)) = do
    GM.basicUnsafeCopy a b
    GM.basicUnsafeCopy (MV as) (MV bs)
  {-# INLINE basicUnsafeCopy #-}

  basicUnsafeMove (MV (MVectorVal a :& as)) (MV (MVectorVal b :& bs)) = do
    GM.basicUnsafeMove a b
    GM.basicUnsafeMove (MV as) (MV bs)
  {-# INLINE basicUnsafeMove #-}

  basicUnsafeGrow :: forall m. PrimMonad m => MVector (PrimState m) (Rec Identity (r ': s ': rs)) -> Int -> m (MVector (PrimState m) (Rec Identity (r ': s ': rs)))
  basicUnsafeGrow (MV (MVectorVal v :& vrs)) n = do
    r <- GM.basicUnsafeGrow v n
    rs <- GM.basicUnsafeGrow (MV vrs) n
    return (MV (MVectorVal r :& stripMV (Proxy :: Proxy m) rs))
  {-# INLINE basicUnsafeGrow #-}

#if MIN_VERSION_vector(0,11,0)
  basicInitialize (MV (MVectorVal v :& rs)) = do
    GM.basicInitialize v
    GM.basicInitialize (MV rs)
  {-# INLINE basicInitialize #-}
#endif

data Vector :: * -> * where
  V :: !(Rec VectorVal rs) -> Vector (Rec Identity rs)
  deriving Typeable

type instance G.Mutable Vector = MVector 

instance ( HasDefaultVector r
         )
    => G.Vector Vector (Rec Identity (r ': '[])) where
  basicUnsafeFreeze (MV (MVectorVal v :& RNil)) = do
    r <- G.basicUnsafeFreeze v
    return (V (VectorVal r :& RNil))
  {-# INLINE basicUnsafeFreeze #-}
  basicUnsafeThaw (V (VectorVal v :& RNil)) = do
    r <- G.basicUnsafeThaw v
    return (MV (MVectorVal r :& RNil))
  {-# INLINE basicUnsafeThaw #-}
  basicLength (V (VectorVal v :& RNil)) = G.basicLength v
  {-# INLINE basicLength #-}
  basicUnsafeSlice s e (V (VectorVal v :& RNil)) = V (VectorVal (G.basicUnsafeSlice s e v) :& RNil)
  {-# INLINE basicUnsafeSlice #-}
  basicUnsafeIndexM (V (VectorVal v :& RNil)) n = do
    r <- G.basicUnsafeIndexM v n
    return (Identity r :& RNil)
  {-# INLINE basicUnsafeIndexM #-}
  basicUnsafeCopy (MV (MVectorVal m :& RNil)) (V (VectorVal v :& RNil)) = G.basicUnsafeCopy m v
  {-# INLINE basicUnsafeCopy #-}
  elemseq (V (VectorVal v :& RNil)) (Identity a :& RNil) b = G.elemseq v a b
  {-# INLINE elemseq #-}


instance ( G.Vector Vector (Rec Identity (s ': rs))
         , HasDefaultVector r
         )
    => G.Vector Vector (Rec Identity (r ': s ': rs)) where
  basicUnsafeFreeze (MV (MVectorVal v :& vrs)) = do
    r <- G.basicUnsafeFreeze v
    rs <- G.basicUnsafeFreeze (MV vrs)
    return (V (VectorVal r :& stripV rs))
  {-# INLINE basicUnsafeFreeze #-}

  basicUnsafeThaw :: forall m. PrimMonad m => Vector (Rec Identity (r ': s ': rs)) -> m (G.Mutable Vector (PrimState m) (Rec Identity (r ': s ': rs)))
  basicUnsafeThaw (V (VectorVal v :& vrs)) = do
    r <- G.basicUnsafeThaw v
    rs <- G.basicUnsafeThaw (V vrs)
    return (MV (MVectorVal r :& stripMV (Proxy :: Proxy m) rs))
  {-# INLINE basicUnsafeThaw #-}

  basicLength (V (VectorVal v :& _)) = G.basicLength v
  {-# INLINE basicLength #-}

  basicUnsafeSlice s e (V (VectorVal v :& rs)) = case G.basicUnsafeSlice s e (V rs) of
    V rsNext -> V (VectorVal (G.basicUnsafeSlice s e v) :& rsNext)
  {-# INLINE basicUnsafeSlice #-}

  basicUnsafeIndexM (V (VectorVal v :& vrs)) n = do
    r <- G.basicUnsafeIndexM v n
    rs <- G.basicUnsafeIndexM (V vrs) n
    return (Identity r :& rs)
  {-# INLINE basicUnsafeIndexM #-}

  basicUnsafeCopy (MV (MVectorVal m :& mrs)) (V (VectorVal v :& vrs)) = do
    G.basicUnsafeCopy m v
    G.basicUnsafeCopy (MV mrs) (V vrs)
  {-# INLINE basicUnsafeCopy #-}

  elemseq (V (VectorVal v :& vrs)) (Identity a :& rs) b = G.elemseq v a (G.elemseq (V vrs) rs b)
  {-# INLINE elemseq #-}
 
-----------------------------------------
-- Helper functions for instance methods
-----------------------------------------
consVec :: Proxy m
        -> G.Mutable (DefaultVector r) (PrimState m) r 
        -> MVector (PrimState m) (Rec Identity rs)
        -> MVector (PrimState m) (Rec Identity (r ': rs))
consVec _ v (MV rs) = MV (MVectorVal v :& rs)
{-# INLINE consVec #-}

stripMV :: Proxy m -> MVector (PrimState m) (Rec Identity rs) -> Rec (MVectorVal (PrimState m)) rs
stripMV _ (MV rs) = rs
{-# INLINE stripMV #-}

stripV :: Vector (Rec Identity rs) -> Rec VectorVal rs
stripV (V rs) = rs
{-# INLINE stripV #-}

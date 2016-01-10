{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}

#ifndef MIN_VERSION_vector
#define MIN_VERSION_vector(x,y,z) 1
#endif

module Data.Vector.Vinyl.Default.NonEmpty.Tagged.Internal
  ( MVector(..)
  , Vector(..)
  ) where

import           Control.Monad
import           Control.Monad.Primitive         (PrimMonad, PrimState)
import           Data.Monoid
import           Data.Typeable                   (Typeable)
import qualified Data.Vector.Generic             as G
import qualified Data.Vector.Generic.Mutable     as GM
import           GHC.Exts                        (Constraint)


import           Data.Proxy
import           Prelude                         hiding (drop, init, length,
                                                  map, null, read, replicate,
                                                  reverse, tail, take)
import           Text.Read

import           Data.Vector.Vinyl.Default.Types (HasDefaultVector (..),
                                                  MVectorVal (..),
                                                  VectorVal (..))
import           Data.Vinyl.Core                 (Rec (..))
import           Data.Vinyl.Functor              (Identity (..))

import           Data.Tagged.Functor             (TaggedFunctor (..))
import           Data.Tuple.TypeLevel            (Snd)
#if MIN_VERSION_vector(0,11,0)
import           Data.Vector.Fusion.Bundle       as Stream
#else
import           Data.Vector.Fusion.Stream       as Stream
#endif

data Vector :: KProxy k -> * -> * where
  V :: forall (k :: KProxy a) (rs :: [(a,*)]).
       !(Rec (TaggedFunctor VectorVal) rs)
    -> Vector k (Rec (TaggedFunctor Identity) rs)
  deriving Typeable

data MVector :: KProxy k -> * -> * -> * where
  MV :: forall (k :: KProxy a) (rs :: [(a,*)]) s.
        !(Rec (TaggedFunctor (MVectorVal s)) rs)
     -> MVector k s (Rec (TaggedFunctor Identity) rs)
  deriving Typeable

instance ( HasDefaultVector (Snd r)
         )
    => GM.MVector (MVector (k :: KProxy a)) (Rec (TaggedFunctor Identity) ((r :: (a,*)) ': '[])) where
  basicLength (MV (TaggedFunctor (MVectorVal v) :& RNil)) = GM.basicLength v
  {-# INLINE basicLength #-}
  basicUnsafeSlice s e (MV (TaggedFunctor (MVectorVal v) :& RNil)) = MV (TaggedFunctor (MVectorVal (GM.basicUnsafeSlice s e v)) :& RNil)
  {-# INLINE basicUnsafeSlice #-}
  basicOverlaps (MV (TaggedFunctor (MVectorVal a) :& RNil)) (MV (TaggedFunctor (MVectorVal b) :& RNil)) = GM.basicOverlaps a b
  {-# INLINE basicOverlaps #-}
  basicUnsafeNew n = do
    r <- GM.basicUnsafeNew n
    return (MV (TaggedFunctor (MVectorVal r) :& RNil))
  {-# INLINE basicUnsafeNew #-}
  basicUnsafeReplicate n (TaggedFunctor (Identity v) :& RNil) = do
    r <- GM.basicUnsafeReplicate n v
    return (MV (TaggedFunctor (MVectorVal r) :& RNil))
  {-# INLINE basicUnsafeReplicate #-}
  basicUnsafeRead (MV (TaggedFunctor (MVectorVal v) :& RNil)) n = do
    r <- GM.basicUnsafeRead v n
    return (TaggedFunctor (Identity r) :& RNil)
  {-# INLINE basicUnsafeRead #-}
  basicUnsafeWrite (MV (TaggedFunctor (MVectorVal v) :& RNil)) n (TaggedFunctor (Identity r) :& RNil) = GM.basicUnsafeWrite v n r
  {-# INLINE basicUnsafeWrite #-}
  basicClear (MV (TaggedFunctor (MVectorVal v) :& RNil)) = GM.basicClear v
  {-# INLINE basicClear #-}
  basicSet (MV (TaggedFunctor (MVectorVal v) :& RNil)) (TaggedFunctor (Identity r) :& RNil) = GM.basicSet v r
  {-# INLINE basicSet #-}
  basicUnsafeCopy (MV (TaggedFunctor (MVectorVal a) :& RNil)) (MV (TaggedFunctor (MVectorVal b) :& RNil)) = GM.basicUnsafeCopy a b
  {-# INLINE basicUnsafeCopy #-}
  basicUnsafeMove (MV (TaggedFunctor (MVectorVal a) :& RNil)) (MV (TaggedFunctor (MVectorVal b) :& RNil)) = GM.basicUnsafeMove a b
  {-# INLINE basicUnsafeMove #-}
  basicUnsafeGrow (MV (TaggedFunctor (MVectorVal v) :& RNil)) n = do
    r <- GM.basicUnsafeGrow v n
    return (MV (TaggedFunctor (MVectorVal r) :& RNil))
  {-# INLINE basicUnsafeGrow #-}
#if MIN_VERSION_vector(0,11,0)
  basicInitialize (MV (TaggedFunctor (MVectorVal v) :& RNil)) = do
    GM.basicInitialize v
  {-# INLINE basicInitialize #-}
#endif

instance ( GM.MVector (MVector k) (Rec (TaggedFunctor Identity) (s ': rs))
         , HasDefaultVector (Snd r)
         )
    => GM.MVector (MVector (k :: KProxy a)) (Rec (TaggedFunctor Identity) ((r :: (a,*)) ': (s :: (a,*)) ': (rs :: [(a,*)]))) where
  basicLength (MV (TaggedFunctor (MVectorVal v) :& _)) = GM.basicLength v
  {-# INLINE basicLength #-}

  basicUnsafeSlice s e (MV (TaggedFunctor (MVectorVal v) :& rs)) = case GM.basicUnsafeSlice s e (kMV (Proxy :: Proxy k) rs) of
    MV rsNext -> kMV (Proxy :: Proxy k)
      (TaggedFunctor (MVectorVal (GM.basicUnsafeSlice s e v)) :& rsNext)
  {-# INLINE basicUnsafeSlice #-}

  basicOverlaps (MV (TaggedFunctor (MVectorVal a) :& as)) (MV (TaggedFunctor (MVectorVal b) :& bs)) =
    GM.basicOverlaps a b || GM.basicOverlaps (kMV (Proxy :: Proxy k) as) (kMV (Proxy :: Proxy k) bs)
  {-# INLINE basicOverlaps #-}

  basicUnsafeNew :: forall m. PrimMonad m
    => Int -> m (MVector k (PrimState m) (Rec (TaggedFunctor Identity) (r ': s ': rs)))
  basicUnsafeNew n =
    consVec (Proxy :: Proxy m) (Proxy :: Proxy r) <$> GM.basicUnsafeNew n <*> GM.basicUnsafeNew n
  {-# INLINE basicUnsafeNew #-}

  basicUnsafeReplicate :: forall m. PrimMonad m
    => Int -> Rec (TaggedFunctor Identity) (r ': s ': rs) -> m (MVector k (PrimState m) (Rec (TaggedFunctor Identity) (r ': s ': rs)))
  basicUnsafeReplicate n (TaggedFunctor (Identity v) :& rs) =
    consVec (Proxy :: Proxy m) (Proxy :: Proxy r) <$> GM.basicUnsafeReplicate n v <*> GM.basicUnsafeReplicate n rs
  {-# INLINE basicUnsafeReplicate #-}

  basicUnsafeRead (MV (TaggedFunctor (MVectorVal v) :& rs)) n = do
    r <- GM.basicUnsafeRead v n
    rs <- GM.basicUnsafeRead (kMV (Proxy :: Proxy k) rs) n
    return (TaggedFunctor (Identity r) :& rs)
  {-# INLINE basicUnsafeRead #-}

  basicUnsafeWrite (MV (TaggedFunctor (MVectorVal v) :& vrs)) n (TaggedFunctor (Identity r) :& rs) = do
    GM.basicUnsafeWrite v n r
    GM.basicUnsafeWrite (kMV (Proxy :: Proxy k) vrs) n rs
  {-# INLINE basicUnsafeWrite #-}

  basicClear (MV (TaggedFunctor (MVectorVal v) :& vrs)) = do
    GM.basicClear v
    GM.basicClear (kMV (Proxy :: Proxy k) vrs)
  {-# INLINE basicClear #-}

  basicSet (MV (TaggedFunctor (MVectorVal v) :& vrs)) (TaggedFunctor (Identity r) :& rs) = do
    GM.basicSet v r
    GM.basicSet (kMV (Proxy :: Proxy k) vrs) rs
  {-# INLINE basicSet #-}

  basicUnsafeCopy (MV (TaggedFunctor (MVectorVal a) :& as)) (MV (TaggedFunctor (MVectorVal b) :& bs)) = do
    GM.basicUnsafeCopy a b
    GM.basicUnsafeCopy (kMV (Proxy :: Proxy k) as) (kMV (Proxy :: Proxy k) bs)
  {-# INLINE basicUnsafeCopy #-}

  basicUnsafeMove (MV (TaggedFunctor (MVectorVal a) :& as)) (MV (TaggedFunctor (MVectorVal b) :& bs)) = do
    GM.basicUnsafeMove a b
    GM.basicUnsafeMove (kMV (Proxy :: Proxy k) as) (kMV (Proxy :: Proxy k) bs)
  {-# INLINE basicUnsafeMove #-}
--
--   basicUnsafeGrow :: forall m. PrimMonad m => MVector (PrimState m) (Rec (TaggedFunctor Identity) (r ': s ': rs)) -> Int -> m (MVector (PrimState m) (Rec (TaggedFunctor Identity) (r ': s ': rs)))
--   basicUnsafeGrow (MV (TaggedFunctor (MVectorVal v) :& vrs)) n = do
--     r <- GM.basicUnsafeGrow v n
--     rs <- GM.basicUnsafeGrow (MV vrs) n
--     return (MV (TaggedFunctor (MVectorVal r) :& stripMV (Proxy :: Proxy m) rs))
--   {-# INLINE basicUnsafeGrow #-}
--
#if MIN_VERSION_vector(0,11,0)
  basicInitialize (MV (TaggedFunctor (MVectorVal v) :& rs)) = do
    GM.basicInitialize v
    GM.basicInitialize (kMV (Proxy :: Proxy k) rs)
  {-# INLINE basicInitialize #-}
#endif


type instance G.Mutable (Vector k) = MVector k

instance ( HasDefaultVector (Snd r)
         )
    => G.Vector (Vector (k :: KProxy a)) (Rec (TaggedFunctor Identity) ((r :: (a,*)) ': '[])) where
  basicUnsafeFreeze (MV (TaggedFunctor (MVectorVal v) :& RNil)) = do
    r <- G.basicUnsafeFreeze v
    return (V (TaggedFunctor (VectorVal r) :& RNil))
  {-# INLINE basicUnsafeFreeze #-}
  basicUnsafeThaw (V (TaggedFunctor (VectorVal v) :& RNil)) = do
    r <- G.basicUnsafeThaw v
    return (MV (TaggedFunctor (MVectorVal r) :& RNil))
  {-# INLINE basicUnsafeThaw #-}
  basicLength (V (TaggedFunctor (VectorVal v) :& RNil)) = G.basicLength v
  {-# INLINE basicLength #-}
  basicUnsafeSlice s e (V (TaggedFunctor (VectorVal v) :& RNil)) = V (TaggedFunctor (VectorVal (G.basicUnsafeSlice s e v)) :& RNil)
  {-# INLINE basicUnsafeSlice #-}
  basicUnsafeIndexM (V (TaggedFunctor (VectorVal v) :& RNil)) n = do
    r <- G.basicUnsafeIndexM v n
    return (TaggedFunctor (Identity r) :& RNil)
  {-# INLINE basicUnsafeIndexM #-}
  basicUnsafeCopy (MV (TaggedFunctor (MVectorVal m) :& RNil)) (V (TaggedFunctor (VectorVal v) :& RNil)) = G.basicUnsafeCopy m v
  {-# INLINE basicUnsafeCopy #-}
  elemseq (V (TaggedFunctor (VectorVal v) :& RNil)) (TaggedFunctor (Identity a) :& RNil) b = G.elemseq v a b
  {-# INLINE elemseq #-}


instance ( G.Vector (Vector k) (Rec (TaggedFunctor Identity) (s ': rs))
         , HasDefaultVector (Snd r)
         )
    => G.Vector (Vector (k :: KProxy a)) (Rec (TaggedFunctor Identity) ((r :: (a,*)) ': (s :: (a,*)) ': (rs :: [(a,*)]))) where
  basicUnsafeFreeze (MV (TaggedFunctor (MVectorVal v) :& vrs)) = do
    r <- G.basicUnsafeFreeze v
    rs <- G.basicUnsafeFreeze (kMV (Proxy :: Proxy k) vrs)
    return (V (TaggedFunctor (VectorVal r) :& stripV rs))
  {-# INLINE basicUnsafeFreeze #-}

  basicUnsafeThaw :: forall m. PrimMonad m => Vector k (Rec (TaggedFunctor Identity) (r ': s ': rs)) -> m (G.Mutable (Vector k) (PrimState m) (Rec (TaggedFunctor Identity) (r ': s ': rs)))
  basicUnsafeThaw (V (TaggedFunctor (VectorVal v) :& vrs)) = do
    r <- G.basicUnsafeThaw v
    rs <- G.basicUnsafeThaw (kV (Proxy :: Proxy k) vrs)
    return (MV (TaggedFunctor (MVectorVal r) :& stripMV (Proxy :: Proxy m) rs))
  {-# INLINE basicUnsafeThaw #-}

  basicLength (V (TaggedFunctor (VectorVal v) :& _)) = G.basicLength v
  {-# INLINE basicLength #-}

  basicUnsafeSlice s e (V (TaggedFunctor (VectorVal v) :& rs)) = case G.basicUnsafeSlice s e (kV (Proxy :: Proxy k) rs) of
    V rsNext -> V (TaggedFunctor (VectorVal (G.basicUnsafeSlice s e v)) :& rsNext)
  {-# INLINE basicUnsafeSlice #-}

  basicUnsafeIndexM (V (TaggedFunctor (VectorVal v) :& vrs)) n = do
    r <- G.basicUnsafeIndexM v n
    rs <- G.basicUnsafeIndexM (kV (Proxy :: Proxy k) vrs) n
    return (TaggedFunctor (Identity r) :& rs)
  {-# INLINE basicUnsafeIndexM #-}

  basicUnsafeCopy (MV (TaggedFunctor (MVectorVal m) :& mrs)) (V (TaggedFunctor (VectorVal v) :& vrs)) = do
    G.basicUnsafeCopy m v
    G.basicUnsafeCopy (kMV (Proxy :: Proxy k) mrs) (kV (Proxy :: Proxy k) vrs)
  {-# INLINE basicUnsafeCopy #-}

  elemseq (V (TaggedFunctor (VectorVal v) :& vrs)) (TaggedFunctor (Identity a) :& rs) b =
    G.elemseq v a (G.elemseq (kV (Proxy :: Proxy k) vrs) rs b)
  {-# INLINE elemseq #-}


-- instance (x ~ Rec Identity rs, Eq x, G.Vector Vector x) => Eq (Vector x) where
--   xs == ys = Stream.eq (G.stream xs) (G.stream ys)
--   {-# INLINE (==) #-}
--
--   xs /= ys = not (Stream.eq (G.stream xs) (G.stream ys))
--   {-# INLINE (/=) #-}
--
--
-- instance (x ~ Rec Identity rs, Ord x, G.Vector Vector x) => Ord (Vector x) where
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



-----------------------------------------
-- Helper functions for instance methods
-----------------------------------------
consVec :: forall (rs :: [(a,*)]) (k :: KProxy a) m r.
     Proxy m
  -> Proxy r
  -> G.Mutable (DefaultVector (Snd r)) (PrimState m) (Snd r)
  -> MVector k (PrimState m) (Rec (TaggedFunctor Identity) rs)
  -> MVector k (PrimState m) (Rec (TaggedFunctor Identity) (r ': rs))
consVec _ _ v (MV rs) = MV (TaggedFunctor (MVectorVal v) :& rs)
{-# INLINE consVec #-}


stripMV :: forall (rs :: [(a,*)]) (k :: KProxy a) m.
  Proxy m
  -> MVector k (PrimState m) (Rec (TaggedFunctor Identity) rs)
  -> Rec (TaggedFunctor (MVectorVal (PrimState m))) rs
stripMV _ (MV rs) = rs
{-# INLINE stripMV #-}

stripV :: forall (rs :: [(a,*)]) (k :: KProxy a).
  Vector k (Rec (TaggedFunctor Identity) rs)
  -> Rec (TaggedFunctor VectorVal) rs
stripV (V rs) = rs
{-# INLINE stripV #-}

kMV :: forall (k :: KProxy a) (rs :: [(a,*)]) s.
     Proxy k
  -> (Rec (TaggedFunctor (MVectorVal s)) rs)
  -> MVector k s (Rec (TaggedFunctor Identity) rs)
kMV _ r = MV r
{-# INLINE kMV #-}

kV :: forall (k :: KProxy a) (rs :: [(a,*)]).
     Proxy k
  -> (Rec (TaggedFunctor VectorVal) rs)
  -> Vector k (Rec (TaggedFunctor Identity) rs)
kV _ r = V r
{-# INLINE kV #-}


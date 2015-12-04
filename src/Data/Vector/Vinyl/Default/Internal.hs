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

module Data.Vector.Vinyl.Default.Internal
  ( MVector(..)
  , MVectorVal(..)
  , Vector(..)
  , HasDefaultVector(..)
  , LAll
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

class ( GM.MVector (G.Mutable (DefaultVector t)) t
      , G.Vector (DefaultVector t) t
      ) => HasDefaultVector t where
  type DefaultVector t :: * -> *

-- | A constraint on each element of a type-level list.
type family LAll c ts :: Constraint where
  LAll c '[] = ()
  LAll c (t ': ts) = (c t, LAll c ts)

-- | The most efficient vector type for each column data type.
instance HasDefaultVector Int where
  type DefaultVector Int = U.Vector
instance HasDefaultVector Bool where
  type DefaultVector Bool = U.Vector
instance HasDefaultVector Float where
  type DefaultVector Float = U.Vector
instance HasDefaultVector Double where
  type DefaultVector Double = U.Vector

newtype MVectorVal s t = MVectorVal { getMVectorVal :: G.Mutable (DefaultVector t) s t }

data MVector :: * -> * -> * where
  MV :: !Int -> !(Rec (MVectorVal s) rs) -> MVector s (Rec Identity rs)
  deriving Typeable

instance GM.MVector MVector (Rec Identity '[]) where
  basicLength (MV i _) = i
  {-# INLINE basicLength #-}
  basicUnsafeSlice _ _ v = v
  {-# INLINE basicUnsafeSlice #-}
  basicOverlaps _ _ = False
  {-# INLINE basicOverlaps #-}
  basicUnsafeNew n = return (MV n RNil)
  {-# INLINE basicUnsafeNew #-}
  basicUnsafeReplicate n _ = return (MV n RNil)
  {-# INLINE basicUnsafeReplicate #-}
  basicUnsafeRead _ _ = return RNil
  {-# INLINE basicUnsafeRead #-}
  basicUnsafeWrite _ _ _ = return ()
  {-# INLINE basicUnsafeWrite #-}
  basicClear _ = return ()
  {-# INLINE basicClear #-}
  basicSet _ _ = return ()
  {-# INLINE basicSet #-}
  basicUnsafeCopy _ _ = return ()
  {-# INLINE basicUnsafeCopy #-}
  basicUnsafeMove _ _ = return ()
  {-# INLINE basicUnsafeMove #-}
  basicUnsafeGrow (MV i _) n = return (MV (i + n) RNil)
  {-# INLINE basicUnsafeGrow #-}
#if MIN_VERSION_vector(0,11,0)
  basicInitialize _ = return ()
  {-# INLINE basicInitialize #-}
#endif
  

instance ( GM.MVector MVector (Rec Identity rs)
         , HasDefaultVector r
         )
    => GM.MVector MVector (Rec Identity (r ': rs)) where
  basicLength (MV i _) = i
  {-# INLINE basicLength #-}

  basicUnsafeSlice s e (MV i (MVectorVal v :& rs)) = case GM.basicUnsafeSlice s e (MV i rs) of
    MV _ rsNext -> MV e (MVectorVal (GM.basicUnsafeSlice s e v) :& rsNext)
  {-# INLINE basicUnsafeSlice #-}

  basicOverlaps (MV i (MVectorVal a :& as)) (MV j (MVectorVal b :& bs)) = 
    GM.basicOverlaps a b || GM.basicOverlaps (MV i as) (MV j bs)
  {-# INLINE basicOverlaps #-}

  basicUnsafeNew :: forall m. PrimMonad m => Int -> m (MVector (PrimState m) (Rec Identity (r ': rs)))
  basicUnsafeNew n = 
    consVec (Proxy :: Proxy m) n <$> GM.basicUnsafeNew n <*> GM.basicUnsafeNew n
  {-# INLINE basicUnsafeNew #-}
  
  basicUnsafeReplicate :: forall m. PrimMonad m => Int -> Rec Identity (r ': rs) -> m (MVector (PrimState m) (Rec Identity (r ': rs)))
  basicUnsafeReplicate n (Identity v :& rs) = 
    consVec (Proxy :: Proxy m) n <$> GM.basicUnsafeReplicate n v <*> GM.basicUnsafeReplicate n rs
  {-# INLINE basicUnsafeReplicate #-}

  basicUnsafeRead (MV i (MVectorVal v :& rs)) n = do
    r <- GM.basicUnsafeRead v n
    rs <- GM.basicUnsafeRead (MV i rs) n
    return (Identity r :& rs)
  {-# INLINE basicUnsafeRead #-}

  basicUnsafeWrite (MV i (MVectorVal v :& vrs)) n (Identity r :& rs) = do
    GM.basicUnsafeWrite v n r
    GM.basicUnsafeWrite (MV i vrs) n rs
  {-# INLINE basicUnsafeWrite #-}

  basicClear (MV i (MVectorVal v :& vrs)) = do
    GM.basicClear v
    GM.basicClear (MV i vrs)
  {-# INLINE basicClear #-}

  basicSet (MV i (MVectorVal v :& vrs)) (Identity r :& rs) = do
    GM.basicSet v r
    GM.basicSet (MV i vrs) rs
  {-# INLINE basicSet #-}

  basicUnsafeCopy (MV i (MVectorVal a :& as)) (MV j (MVectorVal b :& bs)) = do
    GM.basicUnsafeCopy a b
    GM.basicUnsafeCopy (MV i as) (MV j bs)
  {-# INLINE basicUnsafeCopy #-}

  basicUnsafeMove (MV i (MVectorVal a :& as)) (MV j (MVectorVal b :& bs)) = do
    GM.basicUnsafeMove a b
    GM.basicUnsafeMove (MV i as) (MV j bs)
  {-# INLINE basicUnsafeMove #-}

  basicUnsafeGrow :: forall m. PrimMonad m => MVector (PrimState m) (Rec Identity (r ': rs)) -> Int -> m (MVector (PrimState m) (Rec Identity (r ': rs)))
  basicUnsafeGrow (MV i (MVectorVal v :& vrs)) n = do
    r <- GM.basicUnsafeGrow v n
    rs <- GM.basicUnsafeGrow (MV i vrs) n
    return (MV (i + n) (MVectorVal r :& stripMV (Proxy :: Proxy m) rs))
  {-# INLINE basicUnsafeGrow #-}

#if MIN_VERSION_vector(0,11,0)
  basicInitialize (MV i (MVectorVal v :& rs)) = do
    GM.basicInitialize v
    GM.basicInitialize (MV i rs)
  {-# INLINE basicInitialize #-}
#endif

newtype VectorVal t = VectorVal { getVectorVal :: DefaultVector t t }

data Vector :: * -> * where
  V :: !Int -> !(Rec VectorVal rs) -> Vector (Rec Identity rs)
  deriving Typeable

type instance G.Mutable Vector = MVector 

instance G.Vector Vector (Rec Identity '[]) where
  basicUnsafeFreeze (MV n _) = return (V n RNil)
  {-# INLINE basicUnsafeFreeze #-}
  basicUnsafeThaw (V i _) = return (MV i RNil)
  {-# INLINE basicUnsafeThaw #-}
  basicLength (V i _) = i
  {-# INLINE basicLength #-}
  basicUnsafeSlice _ e _ = V e RNil
  {-# INLINE basicUnsafeSlice #-}
  basicUnsafeIndexM _ n = return RNil
  {-# INLINE basicUnsafeIndexM #-}
  basicUnsafeCopy _ _ = return ()
  {-# INLINE basicUnsafeCopy #-}
  elemseq _ RNil b = b
  {-# INLINE elemseq #-}

instance ( G.Vector Vector (Rec Identity rs)
         , HasDefaultVector r
         )
    => G.Vector Vector (Rec Identity (r ': rs)) where
  basicUnsafeFreeze (MV i (MVectorVal v :& vrs)) = do
    r <- G.basicUnsafeFreeze v
    rs <- G.basicUnsafeFreeze (MV i vrs)
    return (V i (VectorVal r :& stripV rs))
  {-# INLINE basicUnsafeFreeze #-}

  basicUnsafeThaw :: forall m. PrimMonad m => Vector (Rec Identity (r ': rs)) -> m (G.Mutable Vector (PrimState m) (Rec Identity (r ': rs)))
  basicUnsafeThaw (V i (VectorVal v :& vrs)) = do
    r <- G.basicUnsafeThaw v
    rs <- G.basicUnsafeThaw (V i vrs)
    return (MV i (MVectorVal r :& stripMV (Proxy :: Proxy m) rs))
  {-# INLINE basicUnsafeThaw #-}

  basicLength (V i _) = i
  {-# INLINE basicLength #-}

  basicUnsafeSlice s e (V i (VectorVal v :& rs)) = case G.basicUnsafeSlice s e (V i rs) of
    V _ rsNext -> V e (VectorVal (G.basicUnsafeSlice s e v) :& rsNext)
  {-# INLINE basicUnsafeSlice #-}

  basicUnsafeIndexM (V i (VectorVal v :& vrs)) n = do
    r <- G.basicUnsafeIndexM v n
    rs <- G.basicUnsafeIndexM (V i vrs) n
    return (Identity r :& rs)
  {-# INLINE basicUnsafeIndexM #-}

  basicUnsafeCopy (MV i (MVectorVal m :& mrs)) (V j (VectorVal v :& vrs)) = do
    G.basicUnsafeCopy m v
    G.basicUnsafeCopy (MV i mrs) (V j vrs)
  {-# INLINE basicUnsafeCopy #-}

  elemseq (V i (VectorVal v :& vrs)) (Identity a :& rs) b = G.elemseq v a (G.elemseq (V i vrs) rs b)
  {-# INLINE elemseq #-}
 
-----------------------------------------
-- Helper functions for instance methods
-----------------------------------------
consVec :: Proxy m
        -> Int 
        -> G.Mutable (DefaultVector r) (PrimState m) r 
        -> MVector (PrimState m) (Rec Identity rs)
        -> MVector (PrimState m) (Rec Identity (r ': rs))
consVec _ n v (MV _ rs) = MV n (MVectorVal v :& rs)
{-# INLINE consVec #-}

stripMV :: Proxy m -> MVector (PrimState m) (Rec Identity rs) -> Rec (MVectorVal (PrimState m)) rs
stripMV _ (MV _ rs) = rs
{-# INLINE stripMV #-}

stripV :: Vector (Rec Identity rs) -> Rec VectorVal rs
stripV (V _ rs) = rs
{-# INLINE stripV #-}

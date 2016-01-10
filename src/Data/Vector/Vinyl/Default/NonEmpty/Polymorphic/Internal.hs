-- Disabled for now since it is not needed
--
-- {-# LANGUAGE CPP                        #-}
-- {-# LANGUAGE DataKinds                  #-}
-- {-# LANGUAGE DeriveDataTypeable         #-}
-- {-# LANGUAGE FlexibleContexts           #-}
-- {-# LANGUAGE FlexibleInstances          #-}
-- {-# LANGUAGE GADTs                      #-}
-- {-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- {-# LANGUAGE InstanceSigs               #-}
-- {-# LANGUAGE KindSignatures             #-}
-- {-# LANGUAGE MultiParamTypeClasses      #-}
-- {-# LANGUAGE RankNTypes                 #-}
-- {-# LANGUAGE ScopedTypeVariables        #-}
-- {-# LANGUAGE TypeFamilies               #-}
-- {-# LANGUAGE TypeOperators              #-}
-- {-# LANGUAGE UndecidableInstances       #-}
--
-- #ifndef MIN_VERSION_vector
-- #define MIN_VERSION_vector(x,y,z) 1
-- #endif
--
-- module Data.Vector.Vinyl.Default.NonEmpty.Polymorphic.Internal
--   ( MVector(..)
--   , Vector(..)
--   , HasDefaultVector(..)
--   ) where
--
-- import           Control.Monad
-- import           Control.Monad.Primitive         (PrimMonad, PrimState)
-- import           Data.Monoid
-- import           Data.Typeable                   (Typeable)
-- import qualified Data.Vector.Generic             as G
-- import qualified Data.Vector.Generic.Mutable     as GM
-- import           GHC.Exts                        (Constraint)
--
-- #if MIN_VERSION_vector(0,11,0)
-- import           Data.Vector.Fusion.Bundle       as Stream
-- #else
-- import           Data.Vector.Fusion.Stream       as Stream
-- #endif
--
-- import           Data.Proxy
-- import           Prelude                         hiding (drop, init, length,
--                                                   map, null, read, replicate,
--                                                   reverse, tail, take)
-- import           Text.Read
--
-- import           Data.Vector.Vinyl.Default.Types (HasDefaultVector (..),
--                                                   MVectorVal (..),
--                                                   VectorVal (..))
-- import           Data.Vinyl.Core                 (Rec (..))
-- import           Data.Vinyl.Functor              (Compose (..), Identity (..))
--
-- data MVector :: * -> * -> * where
--   MV :: !(Rec (Compose (MVectorVal s) f) rs) -> MVector s (Rec f rs)
--   deriving Typeable
--
-- instance ( HasDefaultVector (f r)
--          )
--     => GM.MVector MVector (Rec f (r ': '[])) where
--   basicLength (MV (Compose (MVectorVal v) :& RNil)) = GM.basicLength v
--   {-# INLINE basicLength #-}
--   basicUnsafeSlice s e (MV (Compose (MVectorVal v) :& RNil)) =
--     MV (Compose (MVectorVal (GM.basicUnsafeSlice s e v)) :& RNil)
--   {-# INLINE basicUnsafeSlice #-}
--   basicOverlaps (MV (Compose (MVectorVal a) :& RNil)) (MV (Compose (MVectorVal b) :& RNil)) =
--     GM.basicOverlaps a b
--   {-# INLINE basicOverlaps #-}
--   basicUnsafeNew n = do
--     r <- GM.basicUnsafeNew n
--     return (MV (Compose (MVectorVal r) :& RNil))
--   {-# INLINE basicUnsafeNew #-}
--   basicUnsafeReplicate n (v :& RNil) = do
--     r <- GM.basicUnsafeReplicate n v
--     return (MV (Compose (MVectorVal r) :& RNil))
--   {-# INLINE basicUnsafeReplicate #-}
--   basicUnsafeRead (MV (Compose (MVectorVal v) :& RNil)) n = do
--     r <- GM.basicUnsafeRead v n
--     return (r :& RNil)
--   {-# INLINE basicUnsafeRead #-}
--   basicUnsafeWrite (MV (Compose (MVectorVal v) :& RNil)) n (r :& RNil) = GM.basicUnsafeWrite v n r
--   {-# INLINE basicUnsafeWrite #-}
--   basicClear (MV (Compose (MVectorVal v) :& RNil)) = GM.basicClear v
--   {-# INLINE basicClear #-}
--   basicSet (MV (Compose (MVectorVal v) :& RNil)) (r :& RNil) = GM.basicSet v r
--   {-# INLINE basicSet #-}
--   basicUnsafeCopy (MV (Compose (MVectorVal a) :& RNil)) (MV (Compose (MVectorVal b) :& RNil)) =
--     GM.basicUnsafeCopy a b
--   {-# INLINE basicUnsafeCopy #-}
--   basicUnsafeMove (MV (Compose (MVectorVal a) :& RNil)) (MV (Compose (MVectorVal b) :& RNil)) =
--     GM.basicUnsafeMove a b
--   {-# INLINE basicUnsafeMove #-}
--   basicUnsafeGrow (MV (Compose (MVectorVal v) :& RNil)) n = do
--     r <- GM.basicUnsafeGrow v n
--     return (MV (Compose (MVectorVal r) :& RNil))
--   {-# INLINE basicUnsafeGrow #-}
-- #if MIN_VERSION_vector(0,11,0)
--   basicInitialize (MV (Compose (MVectorVal v) :& RNil)) = do
--     GM.basicInitialize v
--   {-# INLINE basicInitialize #-}
-- #endif
--
-- instance ( GM.MVector MVector (Rec f (s ': rs))
--          , HasDefaultVector (f r)
--          )
--     => GM.MVector MVector (Rec f (r ': s ': rs)) where
--   basicLength (MV (Compose (MVectorVal v) :& _)) = GM.basicLength v
--   {-# INLINE basicLength #-}
--
--   basicUnsafeSlice s e (MV (Compose (MVectorVal v) :& rs)) = case GM.basicUnsafeSlice s e (MV rs) of
--     MV rsNext -> MV (Compose (MVectorVal (GM.basicUnsafeSlice s e v)) :& rsNext)
--   {-# INLINE basicUnsafeSlice #-}
--
--   basicOverlaps (MV (Compose (MVectorVal a) :& as)) (MV (Compose (MVectorVal b) :& bs)) =
--     GM.basicOverlaps a b || GM.basicOverlaps (MV as) (MV bs)
--   {-# INLINE basicOverlaps #-}
--
--   basicUnsafeNew :: forall m. PrimMonad m
--                  => Int -> m (MVector (PrimState m) (Rec f (r ': s ': rs)))
--   basicUnsafeNew n =
--     consVec (Proxy :: Proxy m) <$> GM.basicUnsafeNew n <*> GM.basicUnsafeNew n
--   {-# INLINE basicUnsafeNew #-}
--
--   basicUnsafeReplicate :: forall m. PrimMonad m
--                        => Int -> Rec f (r ': s ': rs)
--                        -> m (MVector (PrimState m) (Rec f (r ': s ': rs)))
--   basicUnsafeReplicate n (v :& rs) =
--     consVec (Proxy :: Proxy m) <$> GM.basicUnsafeReplicate n v <*> GM.basicUnsafeReplicate n rs
--   {-# INLINE basicUnsafeReplicate #-}
--
--   basicUnsafeRead (MV (Compose (MVectorVal v) :& rs)) n = do
--     r <- GM.basicUnsafeRead v n
--     rs <- GM.basicUnsafeRead (MV rs) n
--     return (r :& rs)
--   {-# INLINE basicUnsafeRead #-}
--
--   basicUnsafeWrite (MV (Compose (MVectorVal v) :& vrs)) n (r :& rs) = do
--     GM.basicUnsafeWrite v n r
--     GM.basicUnsafeWrite (MV vrs) n rs
--   {-# INLINE basicUnsafeWrite #-}
--
--   basicClear (MV (Compose (MVectorVal v) :& vrs)) = do
--     GM.basicClear v
--     GM.basicClear (MV vrs)
--   {-# INLINE basicClear #-}
--
--   basicSet (MV (Compose (MVectorVal v) :& vrs)) (r :& rs) = do
--     GM.basicSet v r
--     GM.basicSet (MV vrs) rs
--   {-# INLINE basicSet #-}
--
--   basicUnsafeCopy (MV (Compose (MVectorVal a) :& as)) (MV (Compose (MVectorVal b) :& bs)) = do
--     GM.basicUnsafeCopy a b
--     GM.basicUnsafeCopy (MV as) (MV bs)
--   {-# INLINE basicUnsafeCopy #-}
--
--   basicUnsafeMove (MV (Compose (MVectorVal a) :& as)) (MV (Compose (MVectorVal b) :& bs)) = do
--     GM.basicUnsafeMove a b
--     GM.basicUnsafeMove (MV as) (MV bs)
--   {-# INLINE basicUnsafeMove #-}
--
--   basicUnsafeGrow :: forall m. PrimMonad m
--                   => MVector (PrimState m) (Rec f (r ': s ': rs))
--                   -> Int -> m (MVector (PrimState m) (Rec f (r ': s ': rs)))
--   basicUnsafeGrow (MV (Compose (MVectorVal v) :& vrs)) n = do
--     r <- GM.basicUnsafeGrow v n
--     rs <- GM.basicUnsafeGrow (MV vrs) n
--     return (MV (Compose (MVectorVal r) :& stripMV (Proxy :: Proxy m) rs))
--   {-# INLINE basicUnsafeGrow #-}
--
-- #if MIN_VERSION_vector(0,11,0)
--   basicInitialize (MV (Compose (MVectorVal v) :& rs)) = do
--     GM.basicInitialize v
--     GM.basicInitialize (MV rs)
--   {-# INLINE basicInitialize #-}
-- #endif
--
-- data Vector :: * -> * where
--   V :: !(Rec (Compose VectorVal f) rs) -> Vector (Rec f rs)
--   deriving Typeable
--
-- type instance G.Mutable Vector = MVector
--
-- instance ( HasDefaultVector (f r)
--          )
--     => G.Vector Vector (Rec f (r ': '[])) where
--   basicUnsafeFreeze (MV (Compose (MVectorVal v) :& RNil)) = do
--     r <- G.basicUnsafeFreeze v
--     return (V (Compose (VectorVal r) :& RNil))
--   {-# INLINE basicUnsafeFreeze #-}
--   basicUnsafeThaw (V (Compose (VectorVal v) :& RNil)) = do
--     r <- G.basicUnsafeThaw v
--     return (MV (Compose (MVectorVal r) :& RNil))
--   {-# INLINE basicUnsafeThaw #-}
--   basicLength (V (Compose (VectorVal v) :& RNil)) = G.basicLength v
--   {-# INLINE basicLength #-}
--   basicUnsafeSlice s e (V (Compose (VectorVal v) :& RNil)) =
--     V (Compose (VectorVal (G.basicUnsafeSlice s e v)) :& RNil)
--   {-# INLINE basicUnsafeSlice #-}
--   basicUnsafeIndexM (V (Compose (VectorVal v) :& RNil)) n = do
--     r <- G.basicUnsafeIndexM v n
--     return (r :& RNil)
--   {-# INLINE basicUnsafeIndexM #-}
--   basicUnsafeCopy (MV (Compose (MVectorVal m) :& RNil)) (V (Compose (VectorVal v) :& RNil)) = G.basicUnsafeCopy m v
--   {-# INLINE basicUnsafeCopy #-}
--   elemseq (V (Compose (VectorVal v) :& RNil)) (a :& RNil) b = G.elemseq v a b
--   {-# INLINE elemseq #-}
--
--
-- instance ( G.Vector Vector (Rec f (s ': rs))
--          , HasDefaultVector (f r)
--          )
--     => G.Vector Vector (Rec f (r ': s ': rs)) where
--   basicUnsafeFreeze (MV (Compose (MVectorVal v) :& vrs)) = do
--     r <- G.basicUnsafeFreeze v
--     rs <- G.basicUnsafeFreeze (MV vrs)
--     return (V (Compose (VectorVal r) :& stripV rs))
--   {-# INLINE basicUnsafeFreeze #-}
--
--   basicUnsafeThaw :: forall m. PrimMonad m
--                   => Vector (Rec f (r ': s ': rs))
--                   -> m (G.Mutable Vector (PrimState m) (Rec f (r ': s ': rs)))
--   basicUnsafeThaw (V (Compose (VectorVal v) :& vrs)) = do
--     r <- G.basicUnsafeThaw v
--     rs <- G.basicUnsafeThaw (V vrs)
--     return (MV (Compose (MVectorVal r) :& stripMV (Proxy :: Proxy m) rs))
--   {-# INLINE basicUnsafeThaw #-}
--
--   basicLength (V (Compose (VectorVal v) :& _)) = G.basicLength v
--   {-# INLINE basicLength #-}
--
--   basicUnsafeSlice s e (V (Compose (VectorVal v) :& rs)) = case G.basicUnsafeSlice s e (V rs) of
--     V rsNext -> V (Compose (VectorVal (G.basicUnsafeSlice s e v)) :& rsNext)
--   {-# INLINE basicUnsafeSlice #-}
--
--   basicUnsafeIndexM (V (Compose (VectorVal v) :& vrs)) n = do
--     r <- G.basicUnsafeIndexM v n
--     rs <- G.basicUnsafeIndexM (V vrs) n
--     return (r :& rs)
--   {-# INLINE basicUnsafeIndexM #-}
--
--   basicUnsafeCopy (MV (Compose (MVectorVal m) :& mrs)) (V (Compose (VectorVal v) :& vrs)) = do
--     G.basicUnsafeCopy m v
--     G.basicUnsafeCopy (MV mrs) (V vrs)
--   {-# INLINE basicUnsafeCopy #-}
--
--   elemseq (V (Compose (VectorVal v) :& vrs)) (a :& rs) b = G.elemseq v a (G.elemseq (V vrs) rs b)
--   {-# INLINE elemseq #-}
--
-- -----------------------------------------
-- -- Helper functions for instance methods
-- -----------------------------------------
-- consVec :: Proxy m
--         -> G.Mutable (DefaultVector (f r)) (PrimState m) (f r)
--         -> MVector (PrimState m) (Rec f rs)
--         -> MVector (PrimState m) (Rec f (r ': rs))
-- consVec _ v (MV rs) = MV (Compose (MVectorVal v) :& rs)
-- {-# INLINE consVec #-}
--
-- stripMV :: Proxy m -> MVector (PrimState m) (Rec f rs) -> Rec (Compose (MVectorVal (PrimState m)) f) rs
-- stripMV _ (MV rs) = rs
-- {-# INLINE stripMV #-}
--
-- stripV :: forall (f :: * -> *) rs. Vector (Rec f rs) -> Rec (Compose VectorVal f) rs
-- stripV (V rs) = rs
-- {-# INLINE stripV #-}
--

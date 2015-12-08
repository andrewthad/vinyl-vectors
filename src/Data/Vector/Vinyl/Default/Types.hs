{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Vector.Vinyl.Default.Types
  ( MVectorVal(..)
  , VectorVal(..)
  , HasDefaultVector(..)
  , DefaultBoxed(..)
  ) where

import Data.Default (Default(def))
import qualified Data.Vector as B
import qualified Data.Vector.Unboxed as U
import qualified Data.Text as Text
import qualified Data.Text.Lazy as LText
import qualified Data.ByteString as ByteString
import qualified Data.ByteString.Lazy as LByteString
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Generic as G
import Data.Vector.Vinyl.Default.Types.Deriving (derivingVector)
import Data.Int (Int8,Int16,Int32,Int64)
import Data.Word (Word8,Word16,Word32,Word64)

newtype VectorVal t = VectorVal { getVectorVal :: DefaultVector t t }
newtype MVectorVal s t = MVectorVal { getMVectorVal :: G.Mutable (DefaultVector t) s t }
newtype DefaultBoxed a = DefaultBoxed { getDefaultBoxed :: a }

-- | The most efficient vector type for each column data type.
class ( GM.MVector (G.Mutable (DefaultVector t)) t
      , G.Vector (DefaultVector t) t
      ) => HasDefaultVector t where
  type DefaultVector t :: * -> *

instance HasDefaultVector (DefaultBoxed a) where
  type DefaultVector (DefaultBoxed a) = B.Vector

instance HasDefaultVector Int where
  type DefaultVector Int = U.Vector
instance HasDefaultVector Char where
  type DefaultVector Char = U.Vector
instance HasDefaultVector Bool where
  type DefaultVector Bool = U.Vector
instance HasDefaultVector Float where
  type DefaultVector Float = U.Vector
instance HasDefaultVector Double where
  type DefaultVector Double = U.Vector

instance HasDefaultVector Int8 where
  type DefaultVector Int8 = U.Vector
instance HasDefaultVector Int16 where
  type DefaultVector Int16 = U.Vector
instance HasDefaultVector Int32 where
  type DefaultVector Int32 = U.Vector
instance HasDefaultVector Int64 where
  type DefaultVector Int64 = U.Vector

instance HasDefaultVector Word8 where
  type DefaultVector Word8 = U.Vector
instance HasDefaultVector Word16 where
  type DefaultVector Word16 = U.Vector
instance HasDefaultVector Word32 where
  type DefaultVector Word32 = U.Vector
instance HasDefaultVector Word64 where
  type DefaultVector Word64 = U.Vector

instance HasDefaultVector [a] where
  type DefaultVector [a] = B.Vector

instance HasDefaultVector Text.Text where
  type DefaultVector Text.Text = B.Vector
instance HasDefaultVector LText.Text where
  type DefaultVector LText.Text = B.Vector
instance HasDefaultVector ByteString.ByteString where
  type DefaultVector ByteString.ByteString = B.Vector
instance HasDefaultVector LByteString.ByteString where
  type DefaultVector LByteString.ByteString = B.Vector

instance (HasDefaultVector a, HasDefaultVector b) => HasDefaultVector (a,b) where
  type DefaultVector (a,b) = V_Tuple2

-- instance for tuples
data MV_Tuple2 s c where
  MV_Tuple2 :: MVectorVal s a -> MVectorVal s b -> MV_Tuple2 s (a,b)
data V_Tuple2 c where
  V_Tuple2 :: VectorVal a -> VectorVal b -> V_Tuple2 (a,b)
type instance G.Mutable V_Tuple2 = MV_Tuple2

instance ( HasDefaultVector a
         , HasDefaultVector b
         )
    => GM.MVector MV_Tuple2 (a,b) where
  basicLength (MV_Tuple2 (MVectorVal v) _) = GM.basicLength v
  {-# INLINE basicLength #-}
  basicUnsafeSlice s e (MV_Tuple2 (MVectorVal v) (MVectorVal u)) = MV_Tuple2
    (MVectorVal (GM.basicUnsafeSlice s e v))
    (MVectorVal (GM.basicUnsafeSlice s e u))
  {-# INLINE basicUnsafeSlice #-}
  basicOverlaps (MV_Tuple2 (MVectorVal v1) (MVectorVal u1)) (MV_Tuple2 (MVectorVal v2) (MVectorVal u2)) = 
    GM.basicOverlaps v1 v2 || GM.basicOverlaps u1 u2
  {-# INLINE basicOverlaps #-}
  basicUnsafeNew n = MV_Tuple2 <$> fmap MVectorVal (GM.basicUnsafeNew n)
                               <*> fmap MVectorVal (GM.basicUnsafeNew n)
  {-# INLINE basicUnsafeNew #-}
  basicUnsafeReplicate n (a,b) = 
    MV_Tuple2 <$> (fmap MVectorVal (GM.basicUnsafeReplicate n a))
              <*> (fmap MVectorVal (GM.basicUnsafeReplicate n b))
  {-# INLINE basicUnsafeReplicate #-}
  basicUnsafeRead (MV_Tuple2 (MVectorVal v) (MVectorVal u)) n = do
    v' <- GM.basicUnsafeRead v n
    u' <- GM.basicUnsafeRead u n
    return (v',u')
  {-# INLINE basicUnsafeRead #-}
  basicUnsafeWrite (MV_Tuple2 (MVectorVal v) (MVectorVal u)) n (v',u') = do
    GM.basicUnsafeWrite v n v'
    GM.basicUnsafeWrite u n u'
  {-# INLINE basicUnsafeWrite #-}
  basicClear (MV_Tuple2 (MVectorVal v) (MVectorVal u)) = do
    GM.basicClear v
    GM.basicClear u
  {-# INLINE basicClear #-}
  basicSet (MV_Tuple2 (MVectorVal v) (MVectorVal u)) (v',u') = do
    GM.basicSet v v'
    GM.basicSet u u'
  {-# INLINE basicSet #-}
  basicUnsafeCopy (MV_Tuple2 (MVectorVal v1) (MVectorVal u1)) (MV_Tuple2 (MVectorVal v2) (MVectorVal u2)) = do
    GM.basicUnsafeCopy v1 v2
    GM.basicUnsafeCopy u1 u2
  {-# INLINE basicUnsafeCopy #-}
  basicUnsafeMove (MV_Tuple2 (MVectorVal v1) (MVectorVal u1)) (MV_Tuple2 (MVectorVal v2) (MVectorVal u2)) = do
    GM.basicUnsafeMove v1 v2
    GM.basicUnsafeMove u1 u2
  {-# INLINE basicUnsafeMove #-}
  basicUnsafeGrow (MV_Tuple2 (MVectorVal v) (MVectorVal u)) n = do
    v' <- GM.basicUnsafeGrow v n
    u' <- GM.basicUnsafeGrow u n
    return (MV_Tuple2 (MVectorVal v') (MVectorVal u'))
  {-# INLINE basicUnsafeGrow #-}

#if MIN_VERSION_vector(0,11,0)
  basicInitialize (MV_Tuple2 (MVectorVal v) (MVectorVal u)) = do
    GM.basicInitialize v
    GM.basicInitialize u
  {-# INLINE basicInitialize #-}
#endif
instance ( HasDefaultVector a
         , HasDefaultVector b
         )
    => G.Vector V_Tuple2 (a,b) where
  basicUnsafeFreeze (MV_Tuple2 (MVectorVal v) (MVectorVal u)) = do
    v' <- G.basicUnsafeFreeze v
    u' <- G.basicUnsafeFreeze u
    return (V_Tuple2 (VectorVal v') (VectorVal u'))
  {-# INLINE basicUnsafeFreeze #-}
  basicUnsafeThaw (V_Tuple2 (VectorVal v) (VectorVal u)) = do
    v' <- G.basicUnsafeThaw v
    u' <- G.basicUnsafeThaw u
    return (MV_Tuple2 (MVectorVal v') (MVectorVal u'))
  {-# INLINE basicUnsafeThaw #-}
  basicLength (V_Tuple2 (VectorVal v) _) = G.basicLength v
  {-# INLINE basicLength #-}
  basicUnsafeSlice s e (V_Tuple2 (VectorVal v) (VectorVal u)) = 
    (V_Tuple2 (VectorVal (G.basicUnsafeSlice s e v)) 
              (VectorVal (G.basicUnsafeSlice s e u)))
  {-# INLINE basicUnsafeSlice #-}
  basicUnsafeIndexM (V_Tuple2 (VectorVal v) (VectorVal u)) n = do
    v' <- G.basicUnsafeIndexM v n
    u' <- G.basicUnsafeIndexM u n
    return (v',u')
  {-# INLINE basicUnsafeIndexM #-}
  basicUnsafeCopy (MV_Tuple2 (MVectorVal mv) (MVectorVal mu)) (V_Tuple2 (VectorVal v) (VectorVal u)) = do
    G.basicUnsafeCopy mv v
    G.basicUnsafeCopy mu u
  {-# INLINE basicUnsafeCopy #-}
  elemseq (V_Tuple2 (VectorVal v) (VectorVal u)) (v',u') b = G.elemseq v v' (G.elemseq u u' b)
  {-# INLINE elemseq #-}

class HasVectorizableRepresentation a where
  type VectorizableRepresentation a :: *

-- Derived stuff below here. Basically, we want to get
-- maximally efficient vectors for things like `Maybe a`.
instance HasVectorizableRepresentation (a,b,c) where
  type VectorizableRepresentation (a,b,c) = (a,(b,c))
derivingVector "Tuple3" ''HasDefaultVector ''DefaultVector ''VectorizableRepresentation
  [t| forall a b c. (HasDefaultVector a, HasDefaultVector b, HasDefaultVector c) => (a,b,c) -> (a,(b,c)) |]
  [| \ (a,b,c) -> (a,(b,c)) |]
  [| \ (a,(b,c)) -> (a,b,c) |]
instance (HasDefaultVector a, HasDefaultVector b, HasDefaultVector c) => HasDefaultVector (a,b,c) where
  type DefaultVector (a,b,c) = V_Tuple3

instance HasVectorizableRepresentation (Maybe a) where
  type VectorizableRepresentation (Maybe a) = (Bool,a)
derivingVector "Maybe" ''HasDefaultVector ''DefaultVector ''VectorizableRepresentation
  [t| forall a. (Default a, HasDefaultVector a) => Maybe a -> (Bool, a) |]
  [| maybe (False, def) (\ x -> (True, x)) |]
  [| \ (b, x) -> if b then Just x else Nothing |]
instance (Default a, HasDefaultVector a) => HasDefaultVector (Maybe a) where
  type DefaultVector (Maybe a) = V_Maybe

instance HasVectorizableRepresentation (Either a b) where
  type VectorizableRepresentation (Either a b) = (Bool,(a,b))
derivingVector "Either" ''HasDefaultVector ''DefaultVector ''VectorizableRepresentation
  [t| forall a b. (Default a, Default b, HasDefaultVector a, HasDefaultVector b) => Either a b -> (Bool, (a,b)) |]
  [| either (\a -> (True,(a,def))) (\b -> (True, (def,b))) |]
  [| \ (p, (a,b)) -> if p then Left a else Right b |]
instance (Default a, Default b, HasDefaultVector a, HasDefaultVector b) => HasDefaultVector (Either a b) where
  type DefaultVector (Either a b) = V_Either


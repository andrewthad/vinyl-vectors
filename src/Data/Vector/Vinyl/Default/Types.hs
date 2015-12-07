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
  ) where

import Data.Default (Default(def))
import qualified Data.Vector as B
import qualified Data.Vector.Unboxed as U
import qualified Data.Text as Text
import qualified Data.Text.Lazy as LText
import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Generic as G
import Data.Vector.Vinyl.Default.Types.Deriving (derivingVector)

newtype VectorVal t = VectorVal { getVectorVal :: DefaultVector t t }
newtype MVectorVal s t = MVectorVal { getMVectorVal :: G.Mutable (DefaultVector t) s t }

-- | The most efficient vector type for each column data type.
class ( GM.MVector (G.Mutable (DefaultVector t)) t
      , G.Vector (DefaultVector t) t
      ) => HasDefaultVector t where
  type DefaultVector t :: * -> *

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
instance HasDefaultVector Text.Text where
  type DefaultVector Text.Text = B.Vector
instance HasDefaultVector LText.Text where
  type DefaultVector LText.Text = B.Vector
instance (HasDefaultVector a, HasDefaultVector b) => HasDefaultVector (a,b) where
  type DefaultVector (a,b) = V_Tuple2

-- instance for tuples
data MV_Tuple2 s c where
  MV_Tuple2 :: MVectorVal s a -> MVectorVal s b -> MV_Tuple2 s (a,b)
data V_Tuple2 c where
  V_Tuple2 :: VectorVal a -> VectorVal b -> V_Tuple2 (a,b)
instance ( HasDefaultVector a
         , HasDefaultVector b
         )
    => GM.MVector MV_Tuple2 (a,b) where
instance ( HasDefaultVector a
         , HasDefaultVector b
         )
    => G.Vector V_Tuple2 (a,b) where
type instance G.Mutable V_Tuple2 = MV_Tuple2

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

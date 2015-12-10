{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Vinyl.Named where

import GHC.TypeLits (Symbol,KnownSymbol,symbolVal)
import Data.Map.Strict (Map)
import Data.Proxy (Proxy(Proxy))
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Map.Strict as Map
import GHC.Prim (Any)
import Data.Vinyl.Functor (Compose(..))
import Data.Vinyl.Core (Rec(..))
import Data.Vinyl.TypeLevel (RecAll)
import Data.Vector.Vinyl.TypeLevel (ListAll)
import Data.Dynamic (Dynamic, toDyn, fromDynamic, dynTypeRep)
import Data.Typeable (Typeable)
import Test.QuickCheck.Arbitrary

data NamedType a = NamedType Symbol a

newtype Named (a :: NamedType *) = Named { getNamed :: NamedTypeValue a }
  deriving Typeable
data NamedProxy (a :: NamedType *) = NamedProxy
-- data Named (a :: NamedType *) where
--   Named :: val -> Named ('NamedType key val)
-- data NamedProxy (a :: NamedType *) where
--   NamedProxy :: NamedProxy ('NamedType key val)

instance Show a => Show (Named ('NamedType s a)) where
  show (Named v) = show v
instance Eq a => Eq (Named ('NamedType s a)) where
  Named a == Named b = a == b
instance Arbitrary a => Arbitrary (Named ('NamedType s a)) where
  arbitrary = fmap Named arbitrary
  shrink (Named v) = fmap Named (shrink v)

type family NamedTypeValue (c :: NamedType k) where
  NamedTypeValue ('NamedType s a) = a
type family NamedTypeKey (c :: NamedType *) where
  NamedTypeKey ('NamedType s a) = s

class KnownSymbol (NamedTypeKey t) => NamedTypeKnownSymbol (t :: NamedType *)
instance KnownSymbol (NamedTypeKey t) => NamedTypeKnownSymbol (t :: NamedType *)

class Typeable (NamedTypeValue t) => NamedTypeTypeable (t :: NamedType *)
instance  Typeable (NamedTypeValue t) => NamedTypeTypeable (t :: NamedType *)

class (ca x, cb x) => (ca :&: cb) x
instance (ca x, cb x) => (ca :&: cb) x

-- instance KnownSymbol s => NamedTypeKnownSymbol ('NamedType s a)

toProxyRec :: forall proxy rs. Rec proxy rs -> Rec NamedProxy rs
toProxyRec RNil = RNil
toProxyRec ((_ :: proxy r) :& rs) = 
  (NamedProxy :: NamedProxy r) :& toProxyRec rs

toAnyMap :: ListAll rs NamedTypeKnownSymbol 
         => Rec Named rs -> Map String Any 
toAnyMap RNil = Map.empty
toAnyMap ((Named v :: Named r) :& rs) = 
  Map.insert (symbolVal (Proxy :: Proxy (NamedTypeKey r))) 
             (toAny v) (toAnyMap rs) 

fromAnyMap :: ListAll rs NamedTypeKnownSymbol
           => Rec NamedProxy rs -> Map String Any -> Rec Named rs
fromAnyMap RNil m = if Map.null m then RNil else error "fromAnyMap: expected empty"
fromAnyMap ((NamedProxy :: NamedProxy r) :& rs) m = case Map.lookup keyStr m of
  Just val -> Named (fromAny val) :& fromAnyMap rs (Map.delete keyStr m)
  Nothing -> error ("fromAnyMap: missing key " ++ keyStr)
  where keyStr = (symbolVal (Proxy :: Proxy (NamedTypeKey r)))


toDynamicMap :: ListAll rs (NamedTypeKnownSymbol :&: NamedTypeTypeable)
             => Rec Named rs -> Map String Dynamic
toDynamicMap RNil = Map.empty
toDynamicMap ((Named v :: Named r) :& rs) = 
  Map.insert (symbolVal (Proxy :: Proxy (NamedTypeKey r))) 
             (toDyn v) (toDynamicMap rs) 


fromDynamicMap :: ListAll rs (NamedTypeKnownSymbol :&: NamedTypeTypeable)
               => Rec NamedProxy rs -> Map String Dynamic -> Rec Named rs
fromDynamicMap RNil m = if Map.null m then RNil else error "fromDynamicMap: expected empty" 
fromDynamicMap ((NamedProxy :: NamedProxy r) :& rs) m = case Map.lookup keyStr m of
  Just dval -> case fromDynamic dval of
    Just val -> Named val :& fromDynamicMap rs (Map.delete keyStr m)
    Nothing  -> error ("fromDynamicMap: " ++ keyStr ++ " had type " ++ show (dynTypeRep dval))
  Nothing -> error ("fromDynamicMap: missing key " ++ keyStr)
  where keyStr = (symbolVal (Proxy :: Proxy (NamedTypeKey r)))


-- The dynamic values are of type `f (Named r)` in the resulting `Map`.
composedToDynamicMap :: forall (rs :: [NamedType *]) (f :: * -> *).
  ( ListAll rs (NamedTypeKnownSymbol :&: Typeable)
  , Typeable f
  )
  => Rec (Compose f Named) rs 
  -> Map String Dynamic
composedToDynamicMap RNil = Map.empty
composedToDynamicMap ((Compose fv :: Compose f Named r) :& rs) = 
  Map.insert (symbolVal (Proxy :: Proxy (NamedTypeKey r))) 
             (toDyn fv) (composedToDynamicMap rs) 


composedFromDynamicMap :: 
  ( ListAll rs (NamedTypeKnownSymbol :&: Typeable)
  , Typeable f
  )
  => Rec NamedProxy rs 
  -> Map String Dynamic 
  -> Rec (Compose f Named) rs
composedFromDynamicMap RNil m = if Map.null m then RNil else error "composedFromDynamicMap: expected empty" 
composedFromDynamicMap ((NamedProxy :: NamedProxy r) :& rs) m = case Map.lookup keyStr m of
  Just dval -> case fromDynamic dval of
    Just val -> Compose val :& composedFromDynamicMap rs (Map.delete keyStr m)
    Nothing  -> error ("composedFromDynamicMap: " ++ keyStr ++ " had type " ++ show (dynTypeRep dval))
  Nothing -> error ("composedFromDynamicMap: missing key " ++ keyStr)
  where keyStr = (symbolVal (Proxy :: Proxy (NamedTypeKey r)))


toAny :: a -> Any
toAny = unsafeCoerce

fromAny :: Any -> a
fromAny = unsafeCoerce

-- (Named ('NamedType key val))
-- if Map.null m then RNil else error "fromAnyMap: expected empty"
-- newtype Named (a :: NamedType *) = Named (NamedTypeValue a)


{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Vinyl.Named where

import GHC.TypeLits (Symbol,KnownSymbol,symbolVal,CmpSymbol)
import Data.Map.Strict (Map)
import Data.Proxy (Proxy(Proxy))
import Unsafe.Coerce (unsafeCoerce)
import qualified Data.Map.Strict as Map
import GHC.Prim (Any)
import Data.Vinyl.Functor (Compose(..))
import Data.Vinyl.Core (Rec(..),RecApplicative(rpure))
import Data.Vinyl.TypeLevel (RecAll)
import Data.Vector.Vinyl.TypeLevel (ListAll,Fst,Snd,ConstrainFst,ConstrainSnd)
import Data.Dynamic (Dynamic, toDyn, fromDynamic, dynTypeRep)
import Data.Typeable (Typeable,TypeRep,typeRep,eqT)
import Data.Vinyl.Functor    (Identity)
import Test.QuickCheck.Arbitrary
import GHC.Exts (Constraint)
import Data.Vector.Vinyl.Default.Types (VectorVal(..),HasDefaultVector(..))
import Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Join (indexMany, recFullJoinIndicesImmutable)
import Data.Type.Equality ((:~:)(Refl))
import qualified Data.Vector.Hybrid  as Hybrid
import qualified Data.Vector.Unboxed as U
import Data.Constraint
import Data.Tagged
import Data.Coerce (coerce)

newtype UncurriedTagged (x :: (a,*)) = 
  UncurriedTagged { getUncurriedTagged :: Snd x }
newtype TaggedFunctor (f :: b -> *) (x :: a) (y :: b) =
  TaggedFunctor { getTaggedFunctor :: f y }
newtype UncurriedTaggedFunctor (f :: b -> *) (x :: (a,b)) =
  UncurriedTaggedFunctor { getUncurriedTaggedFunctor :: f (Snd x) }
instance Eq (f (Snd x)) => Eq (UncurriedTaggedFunctor f x) where
  UncurriedTaggedFunctor a == UncurriedTaggedFunctor b = a == b

class TypeString t where
  typeString :: proxy t -> String
instance KnownSymbol t => TypeString (t :: Symbol) where
  typeString _ = symbolVal (Proxy :: Proxy t)
instance (KnownSymbol t,KnownSymbol s) => TypeString ( '(t,s) :: (Symbol,Symbol)) where
  typeString _ = symbolVal (Proxy :: Proxy t) ++ "." ++ symbolVal (Proxy :: Proxy s)

-- data CmpFun               :: * -> *
-- data SymSymbol            :: CmpFun Symbol -> *
-- data SymNamedTypeOfSymbol :: CmpFun (NamedTypeOf Symbol *) -> *
-- data SymNamedType         :: CmpFun (NamedType *) -> *
-- data SymPairNamedType     :: CmpFun (PairNamedType *) -> *
-- 
-- type family ApplyCmp (f :: CmpFun k -> *) (a :: k) (b :: k) :: Ordering
-- type instance ApplyCmp SymNamedType ('NamedType name1 typ1) ('NamedType name2 typ2) = CmpSymbol name1 name2
-- type instance ApplyCmp SymNamedTypeOfSymbol ('NamedTypeOf name1 typ1) ('NamedTypeOf name2 typ2) = CmpSymbol name1 name2
-- 
-- type family ApplyType (f :: CmpFun k -> *) (a :: k) :: *
-- type instance ApplyType SymNamedType ('NamedType name1 typ1) = typ1
-- type instance ApplyType SymNamedTypeOfSymbol ('NamedTypeOf name1 typ1) = typ1
-- 
-- type family ApplyKey (f :: CmpFun k -> *) (a :: k) :: n
-- type instance ApplyKey SymNamedType ('NamedType name1 typ1) = name1
-- type instance ApplyKey SymNamedTypeOfSymbol ('NamedTypeOf name1 typ1) = name1
-- 
-- newtype NamedWith (g :: CmpFun k -> *) (f :: * -> *) (a :: k) = 
--   NamedWith { getNamedWith :: f (ApplyType g a)}
-- 
-- class IsNamedType t where
--   ntName :: proxy t -> String
--   ntType :: proxy t -> TypeRep
--    
-- instance (KnownSymbol (NamedTypeKey s), Typeable (NamedTypeValue s)) => IsNamedType (s :: NamedType *) where
--   ntName _ = symbolVal (Proxy :: Proxy (NamedTypeKey s))
--   ntType _ = typeRep (Proxy :: Proxy (NamedTypeValue s))
-- 
-- instance  (KnownSymbol key, Typeable val) => IsNamedType ('NamedTypeOf key val) where
--   ntName _ = symbolVal (Proxy :: Proxy key)
--   ntType _ = typeRep (Proxy :: Proxy val)
-- 
-- class HasDefaultVector (ApplyType g a) => InnerHasDefaultVector g a
-- instance HasDefaultVector (ApplyType g a) => InnerHasDefaultVector g a

data DictFun (c :: k -> Constraint) (a :: k) where
  DictFun :: Dict (c a) -> DictFun c a

dictFunOf :: Proxy c -> Dict (c a) -> DictFun c a
dictFunOf _ d = DictFun d

reifyDictFun :: ListAll rs c => proxy1 c -> Rec proxy2 rs -> Rec (DictFun c) rs
reifyDictFun _ RNil = RNil
reifyDictFun p (_ :& rs) = DictFun Dict :& reifyDictFun p rs

data NamedTypeOf key val = NamedTypeOf key val
data NamedType a = NamedType Symbol a
data PairNamedType a = PairNamedType Symbol Symbol a

newtype NamedValue (a :: NamedType *) = NamedValue { getNamedValue :: NamedTypeValue a }
  deriving Typeable

newtype Named (f :: * -> *) (a :: NamedType *) = 
  Named { getNamed :: f (NamedTypeValue a)}

deriving instance Eq (f (NamedTypeValue a)) => Eq (Named f a)
deriving instance Ord (f (NamedTypeValue a)) => Ord (Named f a)

instance Show a => Show (NamedValue ('NamedType s a)) where
  show (NamedValue v) = show v
instance Eq a => Eq (NamedValue ('NamedType s a)) where
  NamedValue a == NamedValue b = a == b
instance Arbitrary a => Arbitrary (NamedValue ('NamedType s a)) where
  arbitrary = fmap NamedValue arbitrary
  shrink (NamedValue v) = fmap NamedValue (shrink v)

type family NamedTypeValue (c :: NamedType k) where
  NamedTypeValue ('NamedType s a) = a
type family NamedTypeKey (c :: NamedType *) where
  NamedTypeKey ('NamedType s a) = s
type family NamedTypeValuesAll (rs :: [NamedType *]) (c :: * -> Constraint) :: Constraint where
  NamedTypeValuesAll '[] c = ()
  NamedTypeValuesAll (r ': rs) c = (c (NamedTypeValue r), NamedTypeValuesAll rs c)
type family NamedTypeKeysAll (rs :: [NamedType *]) (c :: Symbol -> Constraint) :: Constraint where
  NamedTypeKeysAll '[] c = ()
  NamedTypeKeysAll (r ': rs) c = (c (NamedTypeKey r), NamedTypeKeysAll rs c)

type family ZipNames (ks :: [k]) (vs :: [v]) where
  ZipNames '[] '[] = '[]
  ZipNames (k ': ks) (v ': vs) = ('(k,v) ': ZipNames ks vs)
type family NamedTypeWithValuesAll (f :: CmpFun k -> *) (rs :: [k]) (c :: * -> Constraint) :: Constraint where
  NamedTypeWithValuesAll f '[] c = ()
  NamedTypeWithValuesAll f (r ': rs) c = (c (ApplyType f r), NamedTypeWithValuesAll f rs c)

class KnownSymbol (NamedTypeKey t) => NamedTypeKnownSymbol (t :: NamedType *)
instance KnownSymbol (NamedTypeKey t) => NamedTypeKnownSymbol (t :: NamedType *)

class Typeable (NamedTypeValue t) => NamedTypeTypeable (t :: NamedType *)
instance Typeable (NamedTypeValue t) => NamedTypeTypeable (t :: NamedType *)

class (ca x, cb x) => (ca :&: cb) x
instance (ca x, cb x) => (ca :&: cb) x

-- instance KnownSymbol s => NamedTypeKnownSymbol ('NamedType s a)

-- toProxyRec :: forall proxy rs. Rec proxy rs -> Rec NamedProxy rs
-- toProxyRec RNil = RNil
-- toProxyRec ((_ :: proxy r) :& rs) = 
--   (NamedProxy :: NamedProxy r) :& toProxyRec rs

toAnyMap :: ListAll rs NamedTypeKnownSymbol 
         => Rec NamedValue rs -> Map String Any 
toAnyMap RNil = Map.empty
toAnyMap ((NamedValue v :: NamedValue r) :& rs) = 
  Map.insert (symbolVal (Proxy :: Proxy (NamedTypeKey r))) 
             (toAny v) 
             (toAnyMap rs) 

fromAnyMap :: ListAll rs NamedTypeKnownSymbol
           => Rec proxy rs -> Map String Any -> Rec NamedValue rs
fromAnyMap RNil m = if Map.null m then RNil else error "fromAnyMap: expected empty"
fromAnyMap ((_ :: proxy r) :& rs) m = case Map.lookup keyStr m of
  Just val -> NamedValue (fromAny val) :& fromAnyMap rs (Map.delete keyStr m)
  Nothing -> error ("fromAnyMap: missing key " ++ keyStr)
  where keyStr = (symbolVal (Proxy :: Proxy (NamedTypeKey r)))


toDynamicMap :: ListAll rs (NamedTypeKnownSymbol :&: NamedTypeTypeable)
             => Rec NamedValue rs -> Map String Dynamic
toDynamicMap RNil = Map.empty
toDynamicMap ((NamedValue v :: NamedValue r) :& rs) = 
  Map.insert (symbolVal (Proxy :: Proxy (NamedTypeKey r))) 
             (toDyn v) (toDynamicMap rs) 


fromDynamicMap :: ListAll rs (NamedTypeKnownSymbol :&: NamedTypeTypeable)
               => Rec proxy rs -> Map String Dynamic -> Rec NamedValue rs
fromDynamicMap RNil m = if Map.null m then RNil else error "fromDynamicMap: expected empty" 
fromDynamicMap ((_ :: proxy r) :& rs) m = case Map.lookup keyStr m of
  Just dval -> case fromDynamic dval of
    Just val -> NamedValue val :& fromDynamicMap rs (Map.delete keyStr m)
    Nothing  -> error ("fromDynamicMap: " ++ keyStr ++ " had type " ++ show (dynTypeRep dval))
  Nothing -> error ("fromDynamicMap: missing key " ++ keyStr)
  where keyStr = (symbolVal (Proxy :: Proxy (NamedTypeKey r)))


-- The dynamic values are of type `f (NamedValue r)` in the resulting `Map`.
composedToDynamicMap :: forall (rs :: [NamedType *]) (f :: * -> *).
  ( ListAll rs (NamedTypeKnownSymbol :&: Typeable)
  , Typeable f
  )
  => Rec (Compose f NamedValue) rs 
  -> Map String Dynamic
composedToDynamicMap RNil = Map.empty
composedToDynamicMap ((Compose fv :: Compose f NamedValue r) :& rs) = 
  Map.insert (symbolVal (Proxy :: Proxy (NamedTypeKey r))) 
             (toDyn fv) (composedToDynamicMap rs) 


composedFromDynamicMap :: 
  ( ListAll rs (NamedTypeKnownSymbol :&: Typeable)
  , Typeable f
  )
  => Rec proxy rs 
  -> Map String Dynamic 
  -> Rec (Compose f NamedValue) rs
composedFromDynamicMap RNil m = if Map.null m then RNil else error "composedFromDynamicMap: expected empty" 
composedFromDynamicMap ((_ :: proxy r) :& rs) m = case Map.lookup keyStr m of
  Just dval -> case fromDynamic dval of
    Just val -> Compose val :& composedFromDynamicMap rs (Map.delete keyStr m)
    Nothing  -> error ("composedFromDynamicMap: " ++ keyStr ++ " had type " ++ show (dynTypeRep dval))
  Nothing -> error ("composedFromDynamicMap: missing key " ++ keyStr)
  where keyStr = (symbolVal (Proxy :: Proxy (NamedTypeKey r)))

toAny :: a -> Any
toAny = unsafeCoerce

fromAny :: Any -> a
fromAny = unsafeCoerce

------------------------------------
-- Vector related stuff
------------------------------------

type ListAllJoinConstraints rs = 
  ( ListAll rs Typeable 
  , ListAll rs Ord
  , ListAll rs HasDefaultVector
  )
type JoinConstraints r = 
  ( Typeable r
  , Ord r
  , HasDefaultVector r
  )

-- everyTypeable :: Rec proxy1 rs -> (ListAll rs Every :- ListAll rs Typeable)
-- everyTypeable RNil = Sub Dict
-- everyTypeable (_ :& rs) = Sub $ case everyTypeable rs of
--   Sub Dict -> Dict

data HiddenVector where
  HiddenVector :: forall (a :: *). 
    JoinConstraints a => 
    VectorVal a -> HiddenVector

data HiddenRec (f :: * -> *) where
  HiddenRec :: forall (rs :: [*]) (f :: * -> *). 
    ListAllJoinConstraints rs => 
    Rec f rs -> HiddenRec f

data ConstrainedHiddenRec (f :: * -> *) (c :: * -> Constraint) where
  ConstrainedHiddenRec :: RecAll f rs c => Rec f rs -> ConstrainedHiddenRec f c

-- This only works if `rs` does not contain duplicate names
indexedHiddenVectorMapsToRec :: forall (rs :: [NamedType *]) proxy.
  ( NamedTypeKeysAll rs KnownSymbol
  , NamedTypeValuesAll rs Typeable
  , NamedTypeValuesAll rs HasDefaultVector
  )
  => Rec proxy rs
  -> [(U.Vector Int, Map String HiddenVector)]
  -> Rec (Named VectorVal) rs
indexedHiddenVectorMapsToRec RNil m = if and (map (Map.null . snd) m) then RNil else error "indexedHiddenVectorMapsToRec: should be empty"
indexedHiddenVectorMapsToRec ((_ :: proxy r) :& rs) m = case lookupHelper keyStr m of
  (i,HiddenVector (VectorVal v :: VectorVal a), mnext) -> case (eqT :: Maybe (NamedTypeValue r :~: a)) of
    Just Refl -> Named (VectorVal (indexMany i v)) :& indexedHiddenVectorMapsToRec rs mnext
    Nothing   -> error ("indexedHiddenVectorMapsToRec: " ++ keyStr ++ " had type " ++ show (typeRep (Proxy :: Proxy a)))
  where 
  keyStr = (symbolVal (Proxy :: Proxy (NamedTypeKey r)))

-- unchecked, still needs to be written
lookupHelper :: String -> [(a, Map String b)] -> (a,b,[(a,Map String b)])
lookupHelper = error "lookupHelper: write me"

-- This function is partial.
hiddenVectorMapToRec :: forall rs m proxy.
  ( ListAll rs (ConstrainSnd Typeable)
  , ListAll rs (ConstrainFst TypeString)
  )
  => Rec proxy rs
  -> Map String HiddenVector
  -> Rec (UncurriedTaggedFunctor VectorVal) rs
hiddenVectorMapToRec RNil m = if Map.null m then RNil else error "hiddenVectorMapToRec: should be empty"
hiddenVectorMapToRec ((_ :: proxy r) :& rs) m = case Map.lookup keyStr m of 
  Just (HiddenVector (v :: VectorVal a)) -> case (eqT :: Maybe (Snd r :~: a)) of
    Just Refl -> UncurriedTaggedFunctor v :& hiddenVectorMapToRec rs (Map.delete keyStr m)
    Nothing   -> error ("hiddenVectorMapToRec: " ++ keyStr ++ " had type " ++ show (typeRep (Proxy :: Proxy a)))
  Nothing -> error ("hiddenVectorMapToRec: missing key " ++ keyStr)
  where keyStr = (typeString (Proxy :: Proxy (Fst r)))

recToHiddenVectorMap :: forall rs. 
  ( ListAll rs (ConstrainSnd Ord)
  , ListAll rs (ConstrainSnd Typeable)
  , ListAll rs (ConstrainSnd HasDefaultVector)
  , ListAll rs (ConstrainFst TypeString)
  )
  => Rec (UncurriedTaggedFunctor VectorVal) rs 
  -> Map String HiddenVector
recToHiddenVectorMap RNil = Map.empty
recToHiddenVectorMap (u@(UncurriedTaggedFunctor v) :& rs) = 
  Map.insert 
    (typeString (proxyFst u))
    (HiddenVector v)
    (recToHiddenVectorMap rs)

proxyFst :: proxy a -> Proxy (Fst a)
proxyFst _ = Proxy

recToHiddenVectorMap2 :: forall rs g. 
  ( NamedTypeWithValuesAll g rs Ord
  , NamedTypeWithValuesAll g rs Typeable
  , NamedTypeWithValuesAll g rs HasDefaultVector
  , ListAll rs IsNamedType
  )
  => Rec (NamedWith g VectorVal) rs 
  -> Map String HiddenVector
recToHiddenVectorMap2 RNil = Map.empty
recToHiddenVectorMap2 ((NamedWith v :: NamedWith g VectorVal r) :& rs) = 
  Map.insert 
    (ntName (Proxy :: Proxy r))
    (HiddenVector v)
    (recToHiddenVectorMap2 rs)

-- This only works if `rs` does not contain duplicate names
indexedHiddenVectorMapsToRec2 :: forall (rs :: [k]) proxy1 proxy2 (g :: CmpFun k -> *).
  ( ListAll rs IsNamedType
  , NamedTypeWithValuesAll g rs Typeable
  , NamedTypeWithValuesAll g rs HasDefaultVector
  )
  => proxy1 g
  -> Rec proxy2 rs
  -> [(U.Vector Int, Map String HiddenVector)]
  -> Rec (NamedWith g VectorVal) rs
indexedHiddenVectorMapsToRec2 _ RNil m = if and (map (Map.null . snd) m) then RNil else error "indexedHiddenVectorMapsToRec: should be empty"
indexedHiddenVectorMapsToRec2 g ((_ :: proxy2 r) :& rs) m = case lookupHelper keyStr m of
  (i,HiddenVector (VectorVal v :: VectorVal a), mnext) -> case (eqT :: Maybe (ApplyType g r :~: a)) of
    Just Refl -> NamedWith (VectorVal (indexMany i v)) :& indexedHiddenVectorMapsToRec2 g rs mnext
    Nothing   -> error ("indexedHiddenVectorMapsToRec: " ++ keyStr ++ " had type " ++ show (typeRep (Proxy :: Proxy a)))
  where 
  keyStr = ntName (Proxy :: Proxy r)


hiddenVectorsToHiddenRec :: [HiddenVector] -> HiddenRec VectorVal
hiddenVectorsToHiddenRec dvs = case dvs of
  [] -> HiddenRec RNil
  HiddenVector v : dvsNext -> case hiddenVectorsToHiddenRec dvsNext of
    HiddenRec rec -> HiddenRec (v :& rec)



uncheckedFullJoinIndices :: 
     [(String,String)] 
  -> Map String HiddenVector
  -> Map String HiddenVector
  -> Hybrid.Vector U.Vector U.Vector (Int,Int)
uncheckedFullJoinIndices matchedCols aMap bMap = r
  where
  aHRec = hiddenVectorsToHiddenRec (uncheckedLookupMany (map fst matchedCols) aMap)
  bHRec = hiddenVectorsToHiddenRec (uncheckedLookupMany (map snd matchedCols) bMap)
  r = uncheckedHiddenRecCoersion aHRec bHRec 
      (\a b -> case a of
        RNil -> error "uncheckedFullJoinIndices: empty record"
        _ :& _ -> recFullJoinIndicesImmutable a b
      )

uncheckedLookupMany :: Ord k => [k] -> Map k v -> [v]
uncheckedLookupMany [] _ = []
uncheckedLookupMany (k : ks) m = case Map.lookup k m of
  Nothing -> error "uncheckedLookupMany: couldn't find key"
  Just v -> v : uncheckedLookupMany ks m

uncheckedHiddenRecCoersion :: forall f a.
     HiddenRec f 
  -> HiddenRec f 
  -> (forall rs. ListAllJoinConstraints rs => Rec f rs -> Rec f rs -> a)
  -> a
uncheckedHiddenRecCoersion (HiddenRec a) (HiddenRec b) f = 
  case uncheckedListEqualitiy a b of
    Refl -> f a b

uncheckedListEqualitiy :: forall proxy1 proxy2 as bs.
  (ListAll as Typeable, ListAll bs Typeable)
  => Rec proxy1 as -> Rec proxy2 bs -> (as :~: bs)
uncheckedListEqualitiy RNil (_ :& _) = error "uncheckedListEqualitiy: mismatched length (left)"
uncheckedListEqualitiy (_ :& _) RNil = error "uncheckedListEqualitiy: mismatched length (right)"
uncheckedListEqualitiy RNil RNil = Refl
uncheckedListEqualitiy (a :& aNext) (b :& bNext) =
  case uncheckedListEqualitiy aNext bNext of
    Refl -> case uncheckedEqT a b of
      Refl -> Refl

uncheckedEqT :: forall proxy1 proxy2 a b. (Typeable a, Typeable b) 
  => proxy1 a -> proxy2 b -> a :~: b
uncheckedEqT _ _ = case (eqT :: Maybe (a :~: b)) of
  Nothing -> error "uncheckedEqT: mismatched types"
  Just Refl -> Refl


-- A convenience function
zipNamesExplicit :: forall f proxy ks vs. 
  Rec proxy ks -> Rec f vs -> Rec (UncurriedTaggedFunctor f) (ZipNames ks vs)
zipNamesExplicit RNil RNil = RNil
zipNamesExplicit ((_ :: proxy k) :& ks) ((r :: f v) :& rs) = 
  (UncurriedTaggedFunctor r :: UncurriedTaggedFunctor f '(k, v)) :& zipNamesExplicit ks rs

zipNames :: forall f proxy ks vs. RecApplicative ks
  => proxy ks -> Rec f vs -> Rec (UncurriedTaggedFunctor f) (ZipNames ks vs)
zipNames _ = zipNamesExplicit (rpure Proxy :: Rec Proxy ks)

class RecApplicativeConstrained (c :: k -> Constraint) (rs :: [k]) where
  rpureConstrained :: Proxy c -> (forall x. c x => f x) -> Rec f rs
instance RecApplicativeConstrained c '[] where
  rpureConstrained _ _ = RNil
instance (RecApplicativeConstrained c rs, c r) => RecApplicativeConstrained c (r ': rs) where
  rpureConstrained p s = s :& rpureConstrained p s

-- rpureConstrained :: RecApplicative rs => Proxy c -> (forall x. c x => f x) -> Rec f rs
-- rpureConstrained _ f = rpureConstrained' f (rpure (DictFun Dict))

rpureConstrained' :: (forall x. c x => f x) -> Rec (DictFun c) rs -> Rec f rs
rpureConstrained' _ RNil = RNil
rpureConstrained' f (DictFun Dict :& rs) = f :& rpureConstrained' f rs

-- data NamedValue (a :: NamedType *) where
--   NamedValue :: val -> NamedValue ('NamedType key val)
-- data NamedProxy (a :: NamedType *) where
--   NamedProxy :: NamedProxy ('NamedType key val)


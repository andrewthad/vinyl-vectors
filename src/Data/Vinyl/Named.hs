{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds         #-}

module Data.Vinyl.Named where

import           Data.Coerce                                         (coerce)
import           Data.Constraint
import           Data.Dynamic                                        (Dynamic, dynTypeRep, fromDynamic,
                                                                      toDyn)
import           Data.List.NonEmpty                                  (NonEmpty ((:|)))
import           Data.List.TypeLevel
import           Data.List.TypeLevel.Constraint
import           Data.Map.Strict                                     (Map)
import qualified Data.Map.Strict                                     as Map
import           Data.Proxy                                          (Proxy (Proxy))
import           Data.Tagged.Functor                                 (TaggedFunctor (..), showSymbolTaggedFunctor)
import           Data.Tuple.TypeLevel
import           Data.Type.Equality                                  ((:~:) (Refl))
import           Data.Typeable                                       (TypeRep,
                                                                      Typeable,
                                                                      eqT,
                                                                      typeRep)
import           Data.TypeString
import qualified Data.Vector.Generic                                 as G
import qualified Data.Vector.Hybrid                                  as Hybrid
import qualified Data.Vector.Unboxed                                 as U
import           Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Join (indexMany, recFullJoinIndicesImmutable)
import           Data.Vector.Vinyl.Default.Types                     (HasDefaultVector (..), VectorVal (..))
import           Data.Vinyl.Core                                     (Rec (..), RecApplicative (rpure),
                                                                      rtraverse)
import           Data.Vinyl.DictFun
import           Data.Vinyl.Functor                                  (Compose (..), Const (..), Identity (..))
import           Data.Vinyl.Functor                                  (Identity)
import           Data.Vinyl.TypeLevel                                (RecAll)
import           GHC.Exts                                            (Constraint)
import           GHC.Prim                                            (Any)
import           GHC.TypeLits                                        (CmpSymbol, KnownSymbol,
                                                                      Symbol,
                                                                      symbolVal)
import           Test.QuickCheck.Arbitrary
import           Unsafe.Coerce                                       (unsafeCoerce)

type RelOpConstraints =
      (ConstrainFst TypeString :&: ConstrainSnd Typeable)
  :&: (ConstrainSnd HasDefaultVector :&: ConstrainSnd Ord :&: ConstrainSnd Show)

newtype UncurriedTagged (x :: (a,*)) =
  UncurriedTagged { getUncurriedTagged :: Snd x }

showSymbolTaggedRec ::
  ( ListAll as (ConstrainFst KnownSymbol)
  , ListAll as (ConstrainSnd Show)
  ) => Rec (TaggedFunctor Identity) as -> String
showSymbolTaggedRec RNil = ""
showSymbolTaggedRec (r :& rs) = showSymbolTaggedFunctor r ++ ", " ++ showSymbolTaggedRec rs

recToProxy :: Rec proxy rs -> Rec Proxy rs
recToProxy RNil = RNil
recToProxy (_ :& rs) = Proxy :& recToProxy rs

rtraverseIdentity :: Applicative f => Rec f rs -> f (Rec Identity rs)
rtraverseIdentity = rtraverse (fmap Identity)

type family PairsSnd (as :: [(k,v)]) :: [v] where
  PairsSnd '[] = '[]
  PairsSnd (a ': as) = Snd a ': PairsSnd as

type family Zip (ks :: [k]) (vs :: [v]) :: [(k,v)] where
  Zip '[] '[] = '[]
  Zip (k ': ks) (v ': vs) = ('(k,v) ': Zip ks vs)

------------------------------------
-- Vector related stuff
------------------------------------

type ListAllJoinConstraints rs =
  ( ListAll rs Typeable
  , ListAll rs Ord
  , ListAll rs HasDefaultVector
  , ListAll rs Show
  )
type JoinConstraints r =
  ( Typeable r
  , Ord r
  , HasDefaultVector r
  , Show r
  )

data HiddenVector where
  HiddenVector :: forall (a :: *).
    JoinConstraints a =>
    VectorVal a -> HiddenVector

instance Show HiddenVector where
  show (HiddenVector (VectorVal a)) = "HiddenVector (" ++ show (G.toList a) ++ ")"

data HiddenRec (f :: * -> *) where
  HiddenRec :: forall (rs :: [*]) (f :: * -> *).
    ListAllJoinConstraints rs =>
    Rec f rs -> HiddenRec f

data NonEmptyHiddenRec (f :: * -> *) where
  NonEmptyHiddenRec :: forall (r :: *) (rs :: [*]) (f :: * -> *).
    ListAllJoinConstraints (r ': rs) =>
    Rec f (r ': rs) -> NonEmptyHiddenRec f

-- data ConstrainedNonEmptyHiddenRec (f :: * -> *) (c :: * -> Constraint) where
--   ConstrainedNonEmptyHiddenRec ::
--     RecAll f (r ': rs) c => Rec f (r ': rs) -> ConstrainedNonEmptyHiddenRec f c

-- This only works if `rs` does not contain duplicate names
-- indexedHiddenVectorMapsToRec :: forall rs proxy.
--   ( ListAll rs (ConstrainFst TypeString)
--   , ListAll rs (ConstrainSnd Typeable)
--   , ListAll rs (ConstrainSnd HasDefaultVector)
--   )
--   => Rec proxy rs
--   -> [(U.Vector Int, Map String HiddenVector)]
--   -> Rec (TaggedFunctor VectorVal) rs
-- indexedHiddenVectorMapsToRec RNil m = if and (map (Map.null . snd) m) then RNil else error "indexedHiddenVectorMapsToRec: should be empty"
-- indexedHiddenVectorMapsToRec ((_ :: proxy r) :& rs) m = case lookupHelper keyStr m of
--   (i,HiddenVector (VectorVal v :: VectorVal a), mnext) -> case (eqT :: Maybe (Snd r :~: a)) of
--     Just Refl -> TaggedFunctor (VectorVal (indexMany i v)) :& indexedHiddenVectorMapsToRec rs mnext
--     Nothing   -> error ("indexedHiddenVectorMapsToRec: " ++ keyStr ++ " had type " ++ show (typeRep (Proxy :: Proxy a)))
--   where
--   keyStr = (typeString (Proxy :: Proxy (Fst r)))

-- This only works if `rs` does not contain duplicate names
indexedHiddenVectorMapsToRec ::
  ( ListAll rs (ConstrainFst TypeString)
  , ListAll rs (ConstrainSnd Typeable)
  , ListAll rs (ConstrainSnd HasDefaultVector)
  )
  => Rec proxy rs
  -> [(U.Vector Int, Map String HiddenVector)]
  -> Rec (TaggedFunctor VectorVal) rs
indexedHiddenVectorMapsToRec prec = go prec . mkMap
  where
  mkMap xs = -- Map.unionsWith (\_ _ -> error "indexedHiddenVectorMapsToRec: duplicate field")
    Map.unions $ map (\(ixs,m) -> fmap (\h -> (ixs,h)) m) xs
  go :: forall rs proxy.
        ( ListAll rs (ConstrainFst TypeString)
        , ListAll rs (ConstrainSnd Typeable)
        , ListAll rs (ConstrainSnd HasDefaultVector)
        )
     => Rec proxy rs
     -> Map String (U.Vector Int, HiddenVector)
     -> Rec (TaggedFunctor VectorVal) rs
  go RNil m = if Map.null m then RNil else error "indexedHiddenVectorMapsToRec: should be empty"
  go ((_ :: proxy r) :& rs) m = case lookupHelper keyStr m of
    ((i,HiddenVector (VectorVal v :: VectorVal a)), mnext) -> case (eqT :: Maybe (Snd r :~: a)) of
      Just Refl -> TaggedFunctor (VectorVal (indexMany i v)) :& go rs mnext
      Nothing   -> error ("indexedHiddenVectorMapsToRec: " ++ keyStr ++ " had type " ++ show (typeRep (Proxy :: Proxy a)))
    where keyStr = (typeString (Proxy :: Proxy (Fst r)))

-- unchecked, still needs to be written
lookupHelper :: String -> Map String a -> (a, Map String a)
lookupHelper name m = case Map.lookup name m of
  Nothing -> error ("lookupHelper: missing name " ++ name)
  Just a  -> (a, Map.delete name m)

-- This function is partial.
hiddenVectorMapToRec :: forall rs m proxy.
  ( ListAll rs (ConstrainSnd Typeable)
  , ListAll rs (ConstrainFst TypeString)
  )
  => Rec proxy rs
  -> Map String HiddenVector
  -> Rec (TaggedFunctor VectorVal) rs
hiddenVectorMapToRec RNil m = if Map.null m then RNil else error "hiddenVectorMapToRec: should be empty"
hiddenVectorMapToRec ((_ :: proxy r) :& rs) m = case Map.lookup keyStr m of
  Just (HiddenVector (v :: VectorVal a)) -> case (eqT :: Maybe (Snd r :~: a)) of
    Just Refl -> TaggedFunctor v :& hiddenVectorMapToRec rs (Map.delete keyStr m)
    Nothing   -> error ("hiddenVectorMapToRec: " ++ keyStr ++ " had type " ++ show (typeRep (Proxy :: Proxy a)))
  Nothing -> error ("hiddenVectorMapToRec: missing key " ++ keyStr)
  where keyStr = (typeString (Proxy :: Proxy (Fst r)))

recToHiddenVectorMap :: forall rs.
  ( ListAll rs RelOpConstraints
  )
  => Rec (TaggedFunctor VectorVal) rs
  -> Map String HiddenVector
recToHiddenVectorMap RNil = Map.empty
recToHiddenVectorMap (u@(TaggedFunctor v) :& rs) =
  Map.insert
    (typeString (proxyFst u))
    (HiddenVector v)
    (recToHiddenVectorMap rs)
  where
  proxyFst :: proxy a -> Proxy (Fst a)
  proxyFst _ = Proxy

hiddenVectorsToHiddenRec :: [HiddenVector] -> HiddenRec VectorVal
hiddenVectorsToHiddenRec dvs = case dvs of
  [] -> HiddenRec RNil
  HiddenVector v : dvsNext -> case hiddenVectorsToHiddenRec dvsNext of
    HiddenRec rec -> HiddenRec (v :& rec)

nonEmptyHiddenVectorsToHiddenRec :: NonEmpty HiddenVector -> NonEmptyHiddenRec VectorVal
nonEmptyHiddenVectorsToHiddenRec (HiddenVector a :| as) = case hiddenVectorsToHiddenRec as of
  HiddenRec rs -> NonEmptyHiddenRec (a :& rs)

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
  Rec proxy ks -> Rec f vs -> Rec (TaggedFunctor f) (Zip ks vs)
zipNamesExplicit RNil RNil = RNil
zipNamesExplicit ((_ :: proxy k) :& ks) ((r :: f v) :& rs) =
  (TaggedFunctor r :: TaggedFunctor f '(k, v)) :& zipNamesExplicit ks rs

zipNames :: forall f proxy ks vs. RecApplicative ks
  => proxy ks -> Rec f vs -> Rec (TaggedFunctor f) (Zip ks vs)
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
rpureConstrained' f (DictFun :& rs) = f :& rpureConstrained' f rs

-- data NamedValue (a :: NamedType *) where
--   NamedValue :: val -> NamedValue ('NamedType key val)
-- data NamedProxy (a :: NamedType *) where
--   NamedProxy :: NamedProxy ('NamedType key val)


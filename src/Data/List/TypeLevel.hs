{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.List.TypeLevel where

import GHC.TypeLits
import Data.Vinyl.Named
import Data.Proxy
import Data.Type.Equality
import Data.Constraint
import Data.Constraint.Unsafe (unsafeCoerceConstraint)
import Data.Vinyl.Core (Rec(..))
import Data.Vector.Vinyl.TypeLevel (ListAll)
import Unsafe.Coerce (unsafeCoerce)
import Data.Typeable
import Data.Vector.Vinyl.Default.Types (HasDefaultVector)

projectRec :: Sublist super sub -> Rec f super -> Rec f sub
projectRec s r = case s of
  SublistNil -> RNil
  SublistBoth snext -> case r of
    rhead :& rtail -> rhead :& projectRec snext rtail
  SublistSuper snext -> case r of
    rhead :& rtail -> projectRec snext rtail

unionRec :: Proxy g 
         -> Rec (DictFun IsNamedType) ls 
         -> Rec (DictFun IsNamedType) rs 
         -> Rec (DictFun IsNamedType) (Union g ls rs)
unionRec _ RNil RNil = RNil
unionRec p (l :& ls) RNil = l :& unionRec p ls RNil
unionRec p RNil (r :& rs) = r :& unionRec p RNil rs
unionRec p ls@(l@(DictFun Dict) :& lsNext) rs@(r@(DictFun Dict) :& rsNext) = case applyCmpString p l r of
  LTy -> r :& unionRec p ls rsNext
  GTy -> l :& unionRec p lsNext rs 
  EQy -> case ntEqT l r of
    Just Refl -> l :& unionRec p lsNext rsNext
    Nothing -> error "unionRec: impossible case"

ordListDict :: ListAll rs c => Proxy c -> OrdList f rs -> Rec (DictFun c) rs
ordListDict p ordList = reifyDictFun p (ordRec ordList)

newtype NamedWith (g :: CmpFun k -> *) (f :: * -> *) (a :: k) = 
  NamedWith { getNamedWith :: f (ApplyType g a)}

class HasDefaultVector (ApplyType g a) => InnerHasDefaultVector g a
instance HasDefaultVector (ApplyType g a) => InnerHasDefaultVector g a


class IsNamedType t where
  ntName :: proxy t -> String
  ntType :: proxy t -> TypeRep
   
instance (KnownSymbol (NamedTypeKey s), Typeable (NamedTypeValue s)) => IsNamedType (s :: NamedType *) where
  ntName _ = symbolVal (Proxy :: Proxy (NamedTypeKey s))
  ntType _ = typeRep (Proxy :: Proxy (NamedTypeValue s))

data CmpFun           :: * -> *
data SymSymbol        :: CmpFun Symbol -> *
data SymNamedType     :: CmpFun (NamedType *) -> *
data SymPairNamedType :: CmpFun (PairNamedType *) -> *

-- data EqFun          :: * -> *
-- data SymNamedTypeEq :: EqFun (NamedType *) -> *

type family ApplyCmp (f :: CmpFun k -> *) (a :: k) (b :: k) :: Ordering
type instance ApplyCmp SymNamedType ('NamedType name1 typ1) ('NamedType name2 typ2) = CmpSymbol name1 name2

type family ApplyType (f :: CmpFun k -> *) (a :: k) :: *
type instance ApplyType SymNamedType ('NamedType name1 typ1) = typ1

type family ApplyKey (f :: CmpFun k -> *) (a :: k) :: n
type instance ApplyKey SymNamedType ('NamedType name1 typ1) = name1

-- | First element of a type pair.
type family Fst k where
    Fst '(a,b) = a

-- |Second element of a type pair.
type family Snd k where
    Snd '(a,b) = b

type ApplyEq f a b k = EqStar (ApplyType f a) (ApplyType f b) k

type family EqStar (a :: *) (b :: *) (r :: k) :: k where
  EqStar a a k = k

-- type family ApplyEq (f :: EqFun k -> *) (a :: k) (b :: k) :: Constraint
-- type instance ApplyEq SymNamedTypeEq ('NamedType name1 typ1) ('NamedType name2 typ2) = typ1 ~ typ2

data ApplyCmpRes (f :: CmpFun k -> *) (a :: k) (b :: k) (r :: Ordering) where
  ApplyCmpRes :: (ApplyCmp f a b ~ r) => ApplyCmpRes f a b r

data OrdList (f :: CmpFun k -> *) (cs :: [k]) where
  OrdListNil    :: OrdList f '[]
  OrdListSingle :: OrdList f '[c]
  OrdListCons   :: ( ApplyCmp f x y ~ GT )
    => OrdList f (y ': cs) 
    -> OrdList f (x ': y ': cs)

--------------------
-- Implicit OrdList 
--------------------
class ImplicitOrdList f rs where 
  implicitOrdList :: OrdList f rs

instance ImplicitOrdList f '[n] where
  implicitOrdList = OrdListSingle

instance (ImplicitOrdList f (n ': ns), ApplyCmp f m n ~ GT) => ImplicitOrdList f (m ': n ': ns) where
  implicitOrdList = OrdListCons (implicitOrdList :: OrdList f (n ': ns))

listHeadProxy :: OrdList f (a ': as) -> Proxy a
listHeadProxy _ = Proxy

listHead2Proxy :: OrdList f (a ': b ': as) -> Proxy b
listHead2Proxy _ = Proxy

data Sublist (super :: [k]) (sub :: [k]) where
  SublistNil   :: Sublist '[] '[]
  SublistSuper :: Sublist super sub -> Sublist (c ': super) sub
  SublistBoth  :: Sublist super sub -> Sublist (c ': super) (c ': sub)

--------------------
-- Implicit Sublist
--------------------
class ImplicitSublist (super :: [k]) (sub :: [k]) where 
  implicitSublist :: Sublist super sub

instance ImplicitSublist '[] '[] where
  implicitSublist = SublistNil

instance {-# OVERLAPPABLE #-} ImplicitSublist super sub => ImplicitSublist (s ': super) sub where
  implicitSublist = SublistSuper (implicitSublist :: Sublist super sub)

instance {-# OVERLAPPING #-} ImplicitSublist super sub => ImplicitSublist (s ': super) (s ': sub) where
  implicitSublist = SublistBoth (implicitSublist :: Sublist super sub)

implicitSublistSub :: ImplicitSublist super sub => Proxy sub -> Sublist super sub
implicitSublistSub _ = implicitSublist

type family IfOrd (a :: Ordering) (lt :: k) (eq :: k) (gt :: k) where 
  IfOrd LT lt eq gt = lt
  IfOrd EQ lt eq gt = eq
  IfOrd GT lt eq gt = gt

ordListTail :: OrdList f (c ': cs) -> OrdList f cs
ordListTail OrdListSingle = OrdListNil
ordListTail (OrdListCons x) = x

data Orderingy (k :: Ordering) where
  LTy :: Orderingy 'LT
  EQy :: Orderingy 'EQ
  GTy :: Orderingy 'GT

-- uses unsafe coerce but it actually safe
applyCmpString :: (IsNamedType a, IsNamedType b) 
  => proxy1 f -> proxy2 a -> proxy3 b -> Orderingy (ApplyCmp f a b)
applyCmpString _ a b = case compare (ntName a) (ntName b) of
  LT -> unsafeCoerce LTy
  EQ -> unsafeCoerce EQy
  GT -> unsafeCoerce GTy

-- uses unsafe coerce but it actually safe
applyCmpTransitive :: Proxy f -> Proxy a -> Proxy b -> Proxy c
  -> (ApplyCmp f a b ~ r, ApplyCmp f b c ~ r) :- (ApplyCmp f a c ~ r)
applyCmpTransitive _ _ _ _ = unsafeCoerceConstraint

-- uses unsafe coerce but it actually safe
ntEqT :: forall a b proxy1 proxy2. (IsNamedType a, IsNamedType b) => proxy1 a -> proxy2 b -> Maybe (a :~: b)
ntEqT _ _ = if ntType (Proxy :: Proxy a) == ntType (Proxy :: Proxy b)
  then Just $ unsafeCoerce Refl
  else Nothing

ordUnion :: OrdList f ls -> OrdList f rs -> OrdList f (Union f ls rs)
ordUnion _ _ = error "ordUnion: Write this function. It's a big one."

ordRec :: OrdList f rs -> Rec Proxy rs
ordRec OrdListNil = RNil
ordRec OrdListSingle = Proxy :& RNil
ordRec (OrdListCons onext) = Proxy :& ordRec onext

ordSublist :: Sublist super sub -> OrdList f super -> OrdList f sub
ordSublist = go
  where
  go :: forall f super sub. Sublist super sub -> OrdList f super -> OrdList f sub
  go SublistNil OrdListNil = OrdListNil
  go (SublistSuper snext) ordList = go snext (ordListTail ordList)
  go ((sublist@(SublistBoth snext))) ordList = case ordList of
    OrdListSingle -> case snext of
      SublistNil -> OrdListSingle 
    OrdListCons onext -> case go snext onext of
      OrdListNil -> OrdListSingle
      ores@OrdListSingle -> case sublistHeadGte snext onext of
        Right Refl -> OrdListCons ores
        Left ApplyCmpRes -> case applyCmpTransitive (Proxy :: Proxy f) (listHeadProxy ordList) (listHead2Proxy ordList) (listHeadProxy ores) of
          Sub Dict -> OrdListCons ores
      ores@(OrdListCons _) -> case sublistHeadGte snext onext of
        Right Refl -> OrdListCons ores
        Left ApplyCmpRes -> case applyCmpTransitive (Proxy :: Proxy f) (listHeadProxy ordList) (listHead2Proxy ordList) (listHeadProxy ores) of
          Sub Dict -> OrdListCons ores
    
sublistHeadGte :: Sublist (superHead ': super) (subHead ': sub) 
               -> OrdList f (superHead ': super) 
               -> Either (ApplyCmpRes f superHead subHead 'GT) (superHead :~: subHead)
sublistHeadGte = go
  where 
  go :: forall superHead super subHead sub f. 
        Sublist (superHead ': super) (subHead ': sub) 
     -> OrdList f (superHead ': super) 
     -> Either (ApplyCmpRes f superHead subHead 'GT) (superHead :~: subHead)
  go (SublistSuper snext) OrdListSingle = error "sublistHeadGte: cannot happen"
  go (SublistSuper snext) (OrdListCons onext) = case go snext onext of
    Left ApplyCmpRes -> case applyCmpTransitive (Proxy :: Proxy f) (Proxy :: Proxy superHead) (listHeadProxy onext) (Proxy :: Proxy subHead) of
      Sub Dict -> Left ApplyCmpRes
    Right Refl -> Left ApplyCmpRes
  go (SublistBoth SublistNil) OrdListSingle = Right Refl
  go (SublistBoth _) (OrdListCons _) = Right Refl

-- This is NOT total.
type family Union (f :: CmpFun k -> *) (a :: [k]) (b :: [k]) :: [k] where
  Union f '[] '[] = '[]
  Union f '[] (b ': bs) = b ': Union f '[] bs 
  Union f (a ': as) '[] = a ': Union f as '[]
  Union f (a ': as) (b ': bs) = 
    IfOrd (ApplyCmp f a b)
      (b ': Union f (a ': as) bs)
      (ApplyEq f a b (a ': Union f as bs))
      (a ': Union f as (b ': bs))


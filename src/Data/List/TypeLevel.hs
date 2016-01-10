{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PolyKinds         #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  Andrew Martin
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Andrew Martin <andrew.thaddeus@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Try to merge some of this into vinyl at some point.
-----------------------------------------------------------------------------

module Data.List.TypeLevel where

import           Data.Constraint
import           Data.Constraint.Unsafe         (unsafeCoerceConstraint)
import           Data.List.TypeLevel.Cmp
import           Data.List.TypeLevel.Constraint
import           Data.List.TypeLevel.Union      (Union)
import           Data.Proxy
import           Data.Tuple.TypeLevel
import           Data.Type.Bool
import           Data.Type.Equality
import           Data.Typeable
import           Data.Vinyl.Core                (Rec (..))
import           Data.Vinyl.DictFun
import           Data.Vinyl.TypeLevel           (RecAll)
import           GHC.Exts                       (Constraint)
import           GHC.TypeLits                   hiding (Nat)
import           Unsafe.Coerce                  (unsafeCoerce)

data Nat = Zero | Succ Nat

data Natty :: Nat -> * where
  Zeroy :: Natty Zero
  Succy :: Natty n -> Natty (Succ n)

class HasNatty (n :: Nat) where
  natty :: Natty n
instance HasNatty Zero where
  natty = Zeroy
instance HasNatty n => HasNatty (Succ n) where
  natty = Succy natty

projectRec :: Sublist super sub -> Rec f super -> Rec f sub
projectRec s r = case s of
  SublistNil -> RNil
  SublistBoth snext -> case r of
    rhead :& rtail -> rhead :& projectRec snext rtail
  SublistSuper snext -> case r of
    rhead :& rtail -> projectRec snext rtail

unionRec ::
     Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable :&: c)) ls
  -> Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable :&: c)) rs
  -> Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable :&: c)) (Union ls rs)
unionRec RNil RNil = RNil
unionRec (l :& ls) RNil = l :& unionRec ls RNil
unionRec RNil (r :& rs) = r :& unionRec RNil rs
unionRec ls@(l@DictFun :& lsNext) rs@(r@DictFun :& rsNext) = case applyCmpString (proxyFst l) (proxyFst r) of
  LTy -> r :& unionRec ls rsNext
  GTy -> l :& unionRec lsNext rs
  EQy -> case eqTProxy (proxySnd l) (proxySnd r) of
    Just Refl -> l :& unionRec lsNext rsNext
    Nothing -> error "unionRec: impossible case"

eqTProxy :: (Typeable a, Typeable b) => proxy1 a -> proxy2 b -> Maybe (a :~: b)
eqTProxy _ _ = eqT

ordListDict :: ListAll rs c => Proxy c -> OrdList rs -> Rec (DictFun c) rs
ordListDict p ordList = reifyDictFun p (ordRec ordList)

data OrdList (cs :: [(m,n)]) where
  OrdListNil    :: OrdList '[]
  OrdListSingle :: OrdList '[c]
  OrdListCons   :: ( Cmp (Fst x) (Fst y) ~ GT )
    => OrdList (y ': cs)
    -> OrdList (x ': y ': cs)

ordListLength :: OrdList rs -> Int
ordListLength = go
  where
  go :: forall a. OrdList a -> Int
  go OrdListNil = 0
  go OrdListSingle = 1
  go (OrdListCons s) = 1 + go s

--------------------
-- Implicit OrdList
--------------------
class ImplicitOrdList rs where
  implicitOrdList :: OrdList rs

instance ImplicitOrdList '[n] where
  implicitOrdList = OrdListSingle

instance (ImplicitOrdList (n ': ns), Cmp (Fst m) (Fst n) ~ GT) => ImplicitOrdList (m ': n ': ns) where
  implicitOrdList = OrdListCons (implicitOrdList :: OrdList (n ': ns))

listHeadProxy :: OrdList (a ': as) -> Proxy a
listHeadProxy _ = Proxy

listHead2Proxy :: OrdList (a ': b ': as) -> Proxy b
listHead2Proxy _ = Proxy

data Sublist (super :: [k]) (sub :: [k]) where
  SublistNil   :: Sublist '[] '[]
  SublistSuper :: Sublist super sub -> Sublist (c ': super) sub
  SublistBoth  :: Sublist super sub -> Sublist (c ': super) (c ': sub)

sublistSuperToRec :: Sublist super sub -> Rec Proxy super
sublistSuperToRec = go
  where
  go :: forall a b. Sublist a b -> Rec Proxy a
  go SublistNil = RNil
  go (SublistSuper s) = Proxy :& go s
  go (SublistBoth s) = Proxy :& go s

sublistSubToRec :: Sublist super sub -> Rec Proxy sub
sublistSubToRec = go
  where
  go :: forall a b. Sublist a b -> Rec Proxy b
  go SublistNil = RNil
  go (SublistSuper s) = go s
  go (SublistBoth s) = Proxy :& go s

sublistSuperLength :: Sublist super sub -> Int
sublistSuperLength = go
  where
  go :: forall a b. Sublist a b -> Int
  go SublistNil = 0
  go (SublistSuper s) = 1 + go s
  go (SublistBoth s) = 1 + go s

sublistSubLength :: Sublist super sub -> Int
sublistSubLength = go
  where
  go :: forall a b. Sublist a b -> Int
  go SublistNil = 0
  go (SublistSuper s) = go s
  go (SublistBoth s) = 1 + go s

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

-- This type family is partial. Both lists should be ordered.
type family SublistLookupMany (super :: [(k,v)]) (sub :: [k]) where
  SublistLookupMany xs '[] = '[]
  SublistLookupMany ('(k,v) ': xs) (k ': ks) = '(k,v) ': SublistLookupMany xs ks
  SublistLookupMany ('(k,v) ': xs) (j ': ks) = SublistLookupMany xs (j ': ks)

-- This type family is partial.
type family SublistLookup (super :: [(k,v)]) (sub :: k) :: v where
  SublistLookup ('(k,v) ': xs) k = v
  SublistLookup ('(k,v) ': xs) j = SublistLookup xs j

-- This type family is partial.
type family SublistLookupManyUnordered (super :: [(k,v)]) (sub :: [k]) :: [(k,v)]where
  SublistLookupManyUnordered xs '[] = '[]
  SublistLookupManyUnordered xs (k ': ks) = '(k,SublistLookup xs k) ': SublistLookupManyUnordered xs ks

implicitSublistSub :: ImplicitSublist super sub => Proxy sub -> Sublist super sub
implicitSublistSub _ = implicitSublist

type family IfOrd (a :: Ordering) (lt :: k) (eq :: k) (gt :: k) where
  IfOrd LT lt eq gt = lt
  IfOrd EQ lt eq gt = eq
  IfOrd GT lt eq gt = gt

ordListTail :: OrdList (c ': cs) -> OrdList cs
ordListTail OrdListSingle = OrdListNil
ordListTail (OrdListCons x) = x

data Orderingy (k :: Ordering) where
  LTy :: Orderingy 'LT
  EQy :: Orderingy 'EQ
  GTy :: Orderingy 'GT

-- uses unsafe coerce but is actually safe
applyCmpString :: (TypeString a, TypeString b)
  => proxy1 a -> proxy2 b -> Orderingy (Cmp a b)
applyCmpString a b = case compare (typeString a) (typeString b) of
  LT -> unsafeCoerce LTy
  EQ -> unsafeCoerce EQy
  GT -> unsafeCoerce GTy

-- uses unsafe coerce but it actually safe
applyCmpTransitive :: proxy1 a -> proxy2 b -> proxy3 c
  -> (Cmp a b ~ r, Cmp b c ~ r) :- (Cmp a c ~ r)
applyCmpTransitive _ _ _ = unsafeCoerceConstraint

invertLt :: proxy1 a -> proxy2 b
  -> (Cmp a b ~ LT) :- (Cmp b a ~ GT)
invertLt _ _ = unsafeCoerceConstraint

invertGt :: proxy1 a -> proxy2 b
  -> (Cmp a b ~ GT) :- (Cmp b a ~ LT)
invertGt _ _ = unsafeCoerceConstraint

-- uses unsafe coerce but it actually safe
-- ntEqT :: forall a b proxy1 proxy2. (TypeString a, TypeString b) => proxy1 a -> proxy2 b -> Maybe (a :~: b)
-- ntEqT _ _ = if ntType (Proxy :: Proxy a) == ntType (Proxy :: Proxy b)
--   then Just $ unsafeCoerce Refl
--   else Nothing

ordUnion :: OrdList ls -> OrdList rs -> OrdList (Union ls rs)
ordUnion _ _ = error "ordUnion: Write this function. It's a big one."

ordRec :: OrdList rs -> Rec Proxy rs
ordRec OrdListNil = RNil
ordRec OrdListSingle = Proxy :& RNil
ordRec (OrdListCons onext) = Proxy :& ordRec onext

sublistTransitive :: Sublist a b -> Sublist b c -> Sublist a c
sublistTransitive ab bc = case ab of
  SublistNil -> case bc of
    SublistNil -> SublistNil
  SublistSuper abNext -> SublistSuper (sublistTransitive abNext bc)
  SublistBoth abNext -> case bc of
    SublistBoth bcNext -> SublistBoth (sublistTransitive abNext bcNext)
    SublistSuper bcNext -> SublistSuper (sublistTransitive abNext bcNext)

ordSublist :: Sublist super sub -> OrdList super -> OrdList sub
ordSublist = go
  where
  go :: forall super sub. Sublist super sub -> OrdList super -> OrdList sub
  go SublistNil OrdListNil = OrdListNil
  go (SublistSuper snext) ordList = go snext (ordListTail ordList)
  go ((sublist@(SublistBoth snext))) ordList = case ordList of
    OrdListSingle -> case snext of
      SublistNil -> OrdListSingle
    OrdListCons onext -> case go snext onext of
      OrdListNil -> OrdListSingle
      ores@OrdListSingle -> case sublistHeadGte snext onext of
        Right Refl -> OrdListCons ores
        Left ApplyCmpRes -> case applyCmpTransitive (proxyFst $ listHeadProxy ordList) (proxyFst $ listHead2Proxy ordList) (proxyFst $ listHeadProxy ores) of
          Sub Dict -> OrdListCons ores
      ores@(OrdListCons _) -> case sublistHeadGte snext onext of
        Right Refl -> OrdListCons ores
        Left ApplyCmpRes -> case applyCmpTransitive (proxyFst $ listHeadProxy ordList) (proxyFst $ listHead2Proxy ordList) (proxyFst $ listHeadProxy ores) of
          Sub Dict -> OrdListCons ores

type family Head (xs :: [k]) :: k where
  Head (x ': xs) = x
type family Tail (xs :: [k]) :: [k] where
  Tail (x ': xs) = xs

data ApplyCmpRes (a :: k) (b :: k) (r :: Ordering) where
  ApplyCmpRes :: (Cmp a b ~ r) => ApplyCmpRes a b r

tupleEquality :: proxy1 a -> proxy2 b
  -> (Fst a ~ Fst b, Snd a ~ Snd b) :- (a ~ b)
tupleEquality _ _ = unsafeCoerceConstraint

typeListHead :: forall x xs proxy. proxy (x ': xs) -> Proxy x
typeListHead _ = Proxy

sublistSuperProxy :: forall super sub. Sublist super sub -> Proxy super
sublistSuperProxy _ = Proxy

sublistSubProxy :: forall super sub. Sublist super sub -> Proxy sub
sublistSubProxy _ = Proxy

sublistHeadGte :: Sublist (superHead ': super) (subHead ': sub)
               -> OrdList (superHead ': super)
               -> Either (ApplyCmpRes (Fst superHead) (Fst subHead) 'GT) (superHead :~: subHead)
sublistHeadGte = go
  where
  go :: forall superHead super subHead sub.
        Sublist (superHead ': super) (subHead ': sub)
     -> OrdList (superHead ': super)
     -> Either (ApplyCmpRes (Fst superHead) (Fst subHead) 'GT) (superHead :~: subHead)
  go (SublistSuper snext) OrdListSingle = error "sublistHeadGte: cannot happen"
  go (SublistSuper snext) (OrdListCons onext) = case go snext onext of
    Left ApplyCmpRes -> case applyCmpTransitive (Proxy :: Proxy (Fst superHead)) (proxyFst (listHeadProxy onext)) (Proxy :: Proxy (Fst subHead)) of
      Sub Dict -> Left ApplyCmpRes
    Right Refl -> Left ApplyCmpRes
  go (SublistBoth SublistNil) OrdListSingle = Right Refl
  go (SublistBoth _) (OrdListCons _) = Right Refl

type family Append (s :: [k]) (t :: [k]) :: [k] where
  Append '[] t = t
  Append (x ': xs) ys = x ': (Append xs ys)

type a ++ b = Append a b

-- This is NOT total.
-- type family Subtraction (a :: [(k,v)]) (b :: [(k,v)]) :: [(k,v)] where
--   Subtraction '[] '[] = '[]
--   Subtraction '[] (b ': bs) = Subtraction '[] bs
--   Subtraction (a ': as) '[] = a ': Subtraction as '[]
--   Subtraction ('Col aName aType ': as) ('Col bName bType ': bs) = IfOrd (CmpName aName bName)
--     (Subtraction ('Col aName aType ': as) bs)
--     (RequiredEqStar aType bType (Subtraction as bs))
--     ('Col aName aType ': (Subtraction as ('Col bName bType ': bs)))

data FilterFlag = FMin | FMax

type family SortMono (a :: [k]) :: [k] where
  SortMono '[] = '[]
  SortMono (k ': xs) = SortMono (FilterMono FMax k xs) ++ '[k] ++ SortMono (FilterMono FMin k xs)

-- rewrite to make this way more efficient
type family FilterMono (f :: FilterFlag) (p :: k) (xs :: [k]) :: [k] where
  FilterMono f p '[] = '[]
  FilterMono FMin p ( k ': xs) = If (Cmp k p == LT) ( k ': (FilterMono FMin p xs)) (FilterMono FMin p xs)
  FilterMono FMax p ( k ': xs) = If (Cmp k p == GT || Cmp k p == EQ) (k ': (FilterMono FMax p xs)) (FilterMono FMax p xs)

type family Sort (a :: [(k,v)]) :: [(k,v)] where
  Sort '[] = '[]
  Sort ( '(k,v) ': xs) = Sort (Filter FMax k xs) ++ '[ '(k,v)] ++ Sort (Filter FMin k xs)

-- rewrite to make this way more efficient
type family Filter (f :: FilterFlag) (p :: k) (xs :: [(k,v)]) :: [(k,v)] where
  Filter f p '[] = '[]
  Filter FMin p ( '(k,v) ': xs) = If (Cmp k p == LT) ( '(k,v) ': (Filter FMin p xs)) (Filter FMin p xs)
  Filter FMax p ( '(k,v) ': xs) = If (Cmp k p == GT || Cmp k p == EQ) ( '(k,v) ': (Filter FMax p xs)) (Filter FMax p xs)


unionSublist ::
     Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)) superA
  -> Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)) superB
  -> OrdList superA -> OrdList superB
  -> Sublist superA subA -> Sublist superB subB
  -> Sublist (Union superA superB) (Union subA subB)
unionSublist = go
  where
  go :: forall superA subA superB subB.
       Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)) superA
    -> Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)) superB
    -> OrdList superA
    -> OrdList superB
    -> Sublist superA subA
    -> Sublist superB subB
    -> Sublist (Union superA superB) (Union subA subB)
  go RNil RNil OrdListNil OrdListNil SublistNil SublistNil = SublistNil
  go (_ :& dls) RNil olnext OrdListNil s SublistNil = case s of
    SublistBoth snext -> SublistBoth
      (go dls RNil (ordListTail olnext) OrdListNil snext SublistNil)
    SublistSuper snext -> SublistSuper
      (go dls RNil (ordListTail olnext) OrdListNil snext SublistNil)
  go RNil (_ :& drs) OrdListNil ornext SublistNil s = case s of
    SublistBoth snext -> SublistBoth
      (go RNil drs OrdListNil (ordListTail ornext) SublistNil snext)
    SublistSuper snext ->
      SublistSuper (go RNil drs OrdListNil (ordListTail ornext) SublistNil snext)
  go dls@(dl@DictFun :& dlsNext) drs@(dr@DictFun :& drsNext) olnext ornext subl subr = case subl of
    SublistBoth slnext -> case subr of
      SublistBoth srnext -> case applyCmpString (proxyFst dl) (proxyFst dr) of
        LTy -> SublistBoth (go dls drsNext olnext (ordListTail ornext) subl srnext)
        GTy -> SublistBoth (go dlsNext drs (ordListTail olnext) ornext slnext subr)
        EQy -> case eqTProxy (proxySnd dl) (proxySnd dr) of
          Just Refl -> SublistBoth (go dlsNext drsNext (ordListTail olnext) (ordListTail ornext) slnext srnext)
          Nothing -> error "unionSublist: impossible case"
      SublistSuper srnext -> case applyCmpString (proxyFst dl) (proxyFst dr) of
        LTy -> SublistSuper (go dls drsNext olnext (ordListTail ornext) subl srnext)
        GTy -> case sublistHeadProof2 dl (Left Dict) subr ornext of
          Right Dict -> SublistBoth (go dlsNext drs (ordListTail olnext) ornext slnext subr)
          Left Dict -> SublistBoth (go dlsNext drs (ordListTail olnext) ornext slnext subr)
        EQy -> case eqToEquality (proxyFst dl) (proxyFst dr) of
          Sub Dict -> case eqTProxy (proxySnd dl) (proxySnd dr) of
            Just Refl -> case srnext of
              SublistNil -> case sublistHeadProof2 dl (Right Dict) srnext (ordListTail ornext) of
                Right Dict -> SublistBoth (go dlsNext drsNext (ordListTail olnext) (ordListTail ornext) slnext srnext)
              SublistSuper _ -> case ornext of
                OrdListCons _ -> case sublistHeadProof2 dl (Left Dict) srnext (ordListTail ornext) of
                  Left Dict -> SublistBoth (go dlsNext drsNext (ordListTail olnext) (ordListTail ornext) slnext srnext)
              SublistBoth _ -> case ornext of
                OrdListCons _ -> case sublistHeadProof2 dl (Left Dict) srnext (ordListTail ornext) of
                  Left Dict -> SublistBoth (go dlsNext drsNext (ordListTail olnext) (ordListTail ornext) slnext srnext)
            Nothing -> error "unionSublist: impossible case"
    SublistSuper slnext -> case subr of
      SublistSuper srnext -> case applyCmpString (proxyFst dl) (proxyFst dr) of
        LTy -> SublistSuper (go dls drsNext olnext (ordListTail ornext) subl srnext)
        GTy -> SublistSuper (go dlsNext drs (ordListTail olnext) ornext slnext subr)
        EQy -> case eqTProxy (proxySnd dl) (proxySnd dr) of
          Just Refl -> SublistSuper (go dlsNext drsNext (ordListTail olnext) (ordListTail ornext) slnext srnext)
          Nothing -> error "unionSublist: impossible case"
      SublistBoth srnext -> case applyCmpString (proxyFst dl) (proxyFst dr) of
        LTy -> case invertLt (proxyFst dl) (proxyFst dr) of
          Sub Dict -> case sublistHeadProof2 dr (Left Dict) subl olnext of
            Right Dict -> SublistBoth (go dls drsNext olnext (ordListTail ornext) subl srnext)
            Left Dict -> case invertGt (proxyFst dr) (proxyFst (typeListHead (sublistSubProxy subl))) of
              Sub Dict -> SublistBoth (go dls drsNext olnext (ordListTail ornext) subl srnext)
        GTy -> SublistSuper (go dlsNext drs (ordListTail olnext) ornext slnext subr)
        EQy -> case eqToEquality (proxyFst dl) (proxyFst dr) of
          Sub Dict -> case eqTProxy (proxySnd dl) (proxySnd dr) of
            Just Refl -> case tupleEquality dl dr of
              Sub Dict -> case slnext of
                SublistNil -> case sublistHeadProof2 dr (Right Dict) slnext (ordListTail olnext) of
                  Right Dict -> SublistBoth (go dlsNext drsNext (ordListTail olnext) (ordListTail ornext) slnext srnext)
                SublistSuper _ -> case olnext of
                  OrdListCons _ -> case sublistHeadProof2 dr (Left Dict) slnext (ordListTail olnext) of
                    Left Dict -> case invertGt (proxyFst dr) (proxyFst (typeListHead (sublistSubProxy subl))) of
                      Sub Dict -> SublistBoth (go dlsNext drsNext (ordListTail olnext) (ordListTail ornext) slnext srnext)
                SublistBoth _ -> case olnext of
                  OrdListCons _ -> case sublistHeadProof2 dr (Left Dict) slnext (ordListTail olnext) of
                    Left Dict -> case invertGt (proxyFst dr) (proxyFst (typeListHead (sublistSubProxy subl))) of
                      Sub Dict -> SublistBoth (go dlsNext drsNext (ordListTail olnext) (ordListTail ornext) slnext srnext)
            Nothing -> error "unionSublist: impossible case"

sublistHeadProof2 :: forall proxy el super sub superHead superOther.
     proxy el
  -> Either ( Dict ( super ~ (superHead ': superOther)
                   , Cmp (Fst el) (Fst superHead) ~ 'GT
                   )
            )
            ( Dict (super ~ '[]))
  -> Sublist super sub
  -> OrdList super
  -> Either (Dict ( sub ~ (Head sub ': Tail sub)
                  , Cmp (Fst el) (Fst (Head sub)) ~ 'GT
                  )
            )
            (Dict (sub ~ '[]))
sublistHeadProof2 el e sublist ordlist = case e of
  Left Dict -> case sublist of
    SublistBoth snext -> Left Dict
    SublistSuper snext -> case ordlist of
      OrdListSingle -> case snext of
        SublistNil -> Right Dict
      OrdListCons ordlistNext ->
        case applyCmpTransitive
               (proxyFst el)
               (proxyFst $ typeListHead $ sublistSuperProxy sublist)
               (proxyFst $ typeListHead $ sublistSuperProxy snext) of
          Sub Dict -> sublistHeadProof2 el (Left Dict) snext ordlistNext
  Right Dict -> case sublist of
    SublistNil -> Right Dict

-- For some reason, these two type families don't work. They wont
-- reduce properly when we learn that ( r ~ r1 ': rs)
--
-- type family ListAllFst (rs :: [(a,b)]) (c :: b -> Constraint) :: Constraint where
--   ListAllFst '[] c = ()
--   ListAllFst ( r ': rs) c = (c (Fst r), ListAllFst rs c)
--
-- type family ListAllSnd (rs :: [(a,b)]) (c :: b -> Constraint) :: Constraint where
--   ListAllSnd '[] c = ()
--   ListAllSnd ( r ': rs) c = (c (Snd r), ListAllSnd rs c)

weakenNil :: RecAll f '[] c1 :- RecAll f '[] c2
weakenNil = Sub Dict

weakenCons :: p rs
           -> c1 (f r) :- c2 (f r)
           -> RecAll f rs c1 :- RecAll f rs c2
           -> RecAll f (r ': rs) c1 :- RecAll f (r ': rs) c2
weakenCons _ entailsF entailsR = Sub $ case (entailsF, entailsR) of
    (Sub Dict, Sub Dict) -> Dict

weakenRecAll :: Rec f rs
             -> (forall a. c1 a :- c2 a)
             -> RecAll f rs c1 :- RecAll f rs c2
weakenRecAll RNil       entails = weakenNil
weakenRecAll (fx :& rs) entails = weakenCons rs entails
                                $ weakenRecAll rs entails

weakenRecDictFun :: forall c1 c2 proxy rs.
     proxy c2
  -> (forall a. c1 a :- c2 a)
  -> Rec (DictFun c1) rs
  -> Rec (DictFun c2) rs
weakenRecDictFun _ _ RNil = RNil
weakenRecDictFun p ent ((DictFun :: DictFun c1 r) :& rs) = case (ent :: (c1 r :- c2 r))  of
  Sub Dict -> DictFun :& weakenRecDictFun p ent rs

recDictFunToDict :: Rec (DictFun c) rs -> Dict (ListAll rs c)
recDictFunToDict RNil = Dict
recDictFunToDict (DictFun :& rs) = case recDictFunToDict rs of
  Dict -> Dict







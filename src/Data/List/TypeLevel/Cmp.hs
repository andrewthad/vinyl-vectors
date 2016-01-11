module Data.List.TypeLevel.Cmp where

import           Data.Constraint
import           Data.Constraint.Unsafe
import           Data.List.TypeLevel.Constraint ((:&:))
import           Data.Tuple.TypeLevel           (ConstrainFst, ConstrainSnd)
import           Data.Type.Equality
import           Data.Typeable                  (Typeable, eqT)
import           Data.TypeString
import           Data.Vinyl.Core                hiding (Dict)
import           Data.Vinyl.DictFun
import           GHC.TypeLits                   (CmpSymbol)
import           Unsafe.Coerce                  (unsafeCoerce)

type family Cmp (a :: k) (b :: k) :: Ordering
type instance Cmp a b = CmpSymbol a b
type CmpDict = DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)

data CmpRes (a :: k) (b :: k) where
  CmpLT :: (Cmp a b ~ 'LT, Cmp b a ~ 'GT) => CmpRes a b
  CmpGT :: (Cmp a b ~ 'GT, Cmp b a ~ 'LT) => CmpRes a b
  CmpEQ :: (Cmp a b ~ 'EQ, Cmp b a ~ 'EQ, a ~ b) => CmpRes a b

type family CmpDual (a :: k) (b :: k) (o :: Ordering) :: Constraint where
  CmpDual a b 'LT = (Cmp a b ~ 'LT, Cmp b a ~ 'GT)
  CmpDual a b 'GT = (Cmp a b ~ 'GT, Cmp b a ~ 'LT)
  CmpDual a b 'EQ = (Cmp a b ~ 'EQ, Cmp b a ~ 'EQ)

compareTypes :: forall proxy1 proxy2 a b.
  (TypeString a, TypeString b)
  => proxy1 a -> proxy2 b -> CmpRes a b
compareTypes a b = case compare (typeString a) (typeString b) of
  LT -> case (unsafeLT a b, unsafeGT b a) of
    (Refl,Refl) -> CmpLT
  GT -> case (unsafeLT b a, unsafeGT a b) of
    (Refl,Refl) -> CmpGT
  EQ -> case (unsafeEQ a b, unsafeEQ b a, unsafeRefl a b) of
    (Refl,Refl,Refl) -> CmpEQ

unsafeLT :: proxy1 a -> proxy2 b -> Cmp a b :~: 'LT
unsafeLT _ _ = unsafeCoerce Refl

unsafeGT :: proxy1 a -> proxy2 b -> Cmp a b :~: 'GT
unsafeGT _ _ = unsafeCoerce Refl

unsafeEQ :: proxy1 a -> proxy2 b -> Cmp a b :~: 'EQ
unsafeEQ _ _ = unsafeCoerce Refl

unsafeRefl :: proxy1 a -> proxy2 b -> a :~: b
unsafeRefl _ _ = unsafeCoerce Refl

eqToEquality :: proxy1 a -> proxy2 b -> (Cmp a b ~ 'EQ) :- (a ~ b)
eqToEquality _ _ = unsafeCoerceConstraint

transitiveLT :: proxy1 a -> proxy2 b -> proxy3 c
  -> (CmpDual a b 'LT, CmpDual b c 'LT) :- (CmpDual a c 'LT)
transitiveLT _ _ _ = unsafeCoerceConstraint

-- uses unsafe coerce but its actually safe
applyCmpTransitive :: proxy1 a -> proxy2 b -> proxy3 c
  -> (Cmp a b ~ r, Cmp b c ~ r) :- (Cmp a c ~ r)
applyCmpTransitive _ _ _ = unsafeCoerceConstraint

eqTProxy :: (Typeable a, Typeable b) => proxy1 a -> proxy2 b -> Maybe (a :~: b)
eqTProxy _ _ = eqT

selfEquality :: proxy1 a -> Cmp a a :~: 'EQ
selfEquality _ = unsafeCoerce Refl


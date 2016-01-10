module Data.List.TypeLevel.Cmp where

import           Data.Constraint
import           Data.Constraint.Unsafe
import           Data.Type.Equality
import           Data.TypeString
import           GHC.TypeLits           (CmpSymbol)
import           Unsafe.Coerce          (unsafeCoerce)

type family Cmp (a :: k) (b :: k) :: Ordering
type instance Cmp a b = CmpSymbol a b

data CmpRes (a :: k) (b :: k) where
  CmpLT :: (Cmp a b ~ 'LT, Cmp b a ~ 'GT) => CmpRes a b
  CmpGT :: (Cmp a b ~ 'GT, Cmp b a ~ 'LT) => CmpRes a b
  CmpEQ :: (Cmp a b ~ 'EQ, Cmp b a ~ 'EQ, a ~ b) => CmpRes a b

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


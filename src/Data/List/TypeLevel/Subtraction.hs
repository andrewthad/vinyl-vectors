module Data.List.TypeLevel.Subtraction where

import           Data.List.TypeLevel.Cmp (Cmp, selfEquality)
import           Data.Tuple.TypeLevel    (Fst, Snd, proxyFst)
import           Data.Type.Equality
import           Data.Vinyl.Core         hiding (Dict)

-- This is NOT total.
type family Subtraction (a :: [(k,v)]) (b :: [(k,v)]) :: [(k,v)] where
  Subtraction '[] '[] = '[]
  Subtraction '[] (b ': bs) = Subtraction '[] bs
  Subtraction (a ': as) '[] = a ': Subtraction as '[]
  Subtraction (a ': as) (b ': bs) = SubtractionCmp (Cmp (Fst a) (Fst b)) a as b bs

type family SubtractionCmp (o :: Ordering) (a :: (k,v)) (as :: [(k,v)]) (b :: (k,v)) (bs :: [(k,v)]) where
  SubtractionCmp 'LT a as b bs = Subtraction (a ': as) bs
  SubtractionCmp 'GT a as b bs = a ': Subtraction as (b ': bs)
  SubtractionCmp 'EQ a as b bs = Subtraction as bs

zeroIdentity :: Rec proxy xs -> Subtraction xs xs :~: '[]
zeroIdentity RNil = Refl
zeroIdentity (r :& rs) = case selfEquality (proxyFst r) of
  Refl -> case zeroIdentity rs of
    Refl -> Refl

leftIdentity :: Rec proxy xs -> Subtraction '[] xs :~: '[]
leftIdentity RNil = Refl
leftIdentity (_ :& rs) = case leftIdentity rs of
  Refl -> Refl

rightIdentity :: Rec proxy xs -> Subtraction xs '[] :~: xs
rightIdentity RNil = Refl
rightIdentity (_ :& rs) = case rightIdentity rs of
  Refl -> Refl

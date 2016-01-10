{-# LANGUAGE PolyKinds #-}

module Data.List.TypeLevel.Subtraction where

import           Data.List.TypeLevel.Cmp (Cmp)
import           Data.Tuple.TypeLevel    (Fst, Snd)

-- This is NOT total.
type family Subtraction (a :: [(k,v)]) (b :: [(k,v)]) :: [(k,v)] where
  Subtraction '[] '[] = '[]
  Subtraction '[] (b ': bs) = b ': Subtraction '[] bs
  Subtraction (a ': as) '[] = a ': Subtraction as '[]
  Subtraction (a ': as) (b ': bs) = SubtractionCmp (Cmp (Fst a) (Fst b)) a as b bs

type family SubtractionCmp (o :: Ordering) (a :: (k,v)) (as :: [(k,v)]) (b :: (k,v)) (bs :: [(k,v)]) where
  SubtractionCmp 'LT a as b bs = Subtraction (a ': as) bs
  SubtractionCmp 'EQ a as b bs = Subtraction as bs
  SubtractionCmp 'GT a as b bs = a ': Subtraction as (b ': bs)

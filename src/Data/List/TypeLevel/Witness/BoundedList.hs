module Data.List.TypeLevel.Witness.BoundedList where

import           Prelude                     hiding (head, tail)

import           Data.Constraint
import           Data.List.TypeLevel.Cmp
import           Data.List.TypeLevel.Witness
import           Data.Proxy
import           Data.Tuple.TypeLevel

increase :: forall a b rs proxy. (CmpDual (Fst a) (Fst b) 'LT)
  => proxy b -> BoundedList a rs -> BoundedList b rs
increase _ BoundedListNil = BoundedListNil
increase b bl@BoundedListCons =
  case transitiveLT (proxyFst $ head bl) (Proxy :: Proxy (Fst a)) (proxyFst b) of
    Sub Dict -> BoundedListCons

toListProxy :: BoundedList a as -> Proxy as
toListProxy _ = Proxy

head :: BoundedList u (a ': as) -> Proxy a
head BoundedListCons = Proxy

getBound :: BoundedList u as -> Proxy u
getBound _ = Proxy

-- boundWith :: proxy a -> BoundedList a (a

-- tail :: BoundedList u (a ': as) -> BoundedList u as


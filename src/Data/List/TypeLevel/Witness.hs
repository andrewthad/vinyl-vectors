module Data.List.TypeLevel.Witness where

import           Data.List.TypeLevel.Cmp
import           Data.Tuple.TypeLevel

data BoundedList (r :: (k,v)) (rs :: [(k,v)]) where
  BoundedListNil  :: BoundedList k '[]
  BoundedListCons :: (CmpDual (Fst x) (Fst y) 'GT)
                  => BoundedList x (y ': xs)

data OrdList (cs :: [(m,n)]) where
  OrdListNil    :: OrdList '[]
  OrdListSingle :: OrdList '[c]
  OrdListCons   :: ( CmpDual (Fst x) (Fst y) 'GT )
    => OrdList (y ': cs)
    -> OrdList (x ': y ': cs)

data Sublist (super :: [k]) (sub :: [k]) where
  SublistNil   :: Sublist '[] '[]
  SublistSuper :: Sublist super sub -> Sublist (c ': super) sub
  SublistBoth  :: Sublist super sub -> Sublist (c ': super) (c ': sub)




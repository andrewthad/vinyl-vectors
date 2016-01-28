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

-- RemoveElem doubles as InsertElem. Mentally flip the way you
-- look at the latter two arguments to see this.
data RemoveElem (r :: k) (rs :: [k]) (ss :: [k]) where
  RemoveElemDone :: RemoveElem r (r ': ss) ss
  RemoveElemNext :: RemoveElem r rs ss -> RemoveElem r (a ': rs) (a ': ss)

-- data InsertElem :: (r :: k) (rs :: [k]) (ss :: [k]) where
--   InsertElemDone :: InsertElem r (r ': ss) ss
--   InsertElemNext :: InsertElem r rs ss -> InsertElem r (a ': rs) (a ': ss)

-- The Next constructor doesn't enforce ordering. This is intentional.
-- This witness should really only be used when an OrdList is available.
data InsertElemOrd (r :: (k,v)) (rs :: [(k,v)]) (ss :: [(k,v)]) where
  InsertElemOrdSpecial   :: SpecialInsert r rs ss -> InsertElemOrd r rs ss
  InsertElemOrdRecursive :: RecursiveInsert r rs ss -> InsertElemOrd r rs ss

data SpecialInsert (r :: (k,v)) (rs :: [(k,v)]) (ss :: [(k,v)]) where
  SpecialInsertFirst  :: (CmpDual (Fst r) (Fst a) 'GT) => SpecialInsert r (a ': as) (r ': a ': as)
  SpecialInsertSingle :: SpecialInsert r '[] '[r]

data RecursiveInsert (r :: (k,v)) (rs :: [(k,v)]) (ss :: [(k,v)]) where
  RecursiveInsertLast   :: (CmpDual (Fst r) (Fst a) 'LT) => RecursiveInsert r '[a] '[a,r]
  RecursiveInsertMiddle ::
    ( CmpDual (Fst r) (Fst a) 'GT
    , CmpDual (Fst r) (Fst b) 'LT
    ) => RecursiveInsert r (b ': a ': as) (b ': r ': a ': as)
  RecursiveInsertNext :: RecursiveInsert r rs ss -> RecursiveInsert r (a ': rs) (a ': ss)



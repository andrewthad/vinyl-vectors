{-# LANGUAGE PolyKinds #-}
module Data.Relation where

import Data.Typeable ( Typeable )
import Data.Vinyl.Named ( RelOpConstraints, recToProxy )
import Data.List.TypeLevel
import Data.Vector.Vinyl.Default.Types ( VectorVal(..) )
import Data.Proxy ( Proxy(..) )
import Data.Vinyl.Core ( Rec(..) )
import Data.Constraint ( type (:-)(Sub), Dict(Dict) )
import Data.Tagged.Functor ( TaggedFunctor(..) )

type MinimalConstraints = 
      ConstrainFst TypeString
  :&: ConstrainSnd Typeable
  :&: ConstrainSnd Ord

data NullRelArity = NullRelOne | NullRelZero
  deriving Show

data Pred (rs :: [(k,*)]) where
  PredNot     :: Pred rs -> Pred rs
  PredOr      :: Sublist cs as -> Sublist cs bs 
              -> Pred as -> Pred bs -> Pred cs
  PredAnd     :: Sublist cs as -> Sublist cs bs
              -> Pred as -> Pred bs -> Pred cs
  PredEqValue :: val -> Pred '[ '(key,val)]
  PredEqCols  :: OrdList '[ '(key1,val), '(key2,val)] 
              -> Pred '[ '(key1,val), '(key2,val)] 

-- Idea for final version of RelOp:
--
--   data Relation (a :: [(k,*)] -> *) rs where
--     RelationNull    :: NullRelArity -> Relation '[]
--     RelationPresent :: a (r ': rs) -> Relation a (r ': rs)
--
--   -- We might want to reify the dictionaries in the
--   -- RelTable data constructor.
--   data RelOp c a rs where
--     RelTable :: ( ListAll rs RelOpConstraints, ListAll rs c)
--       => OrdList rs
--       -> m (Relation a rs)
--       -> RelOp c a rs
--   
--   -- The `m` is optional. Run can be done many ways. If 
--   -- the `a` implies IO, then `m` will probably be IO.
--   -- Actually, `a` doesn't even need to show up in `Relation`.
--   run :: RelOp c a rs -> m (Relation a rs)
--   run :: RelOp c a rs -> m (Relation (Rec (TaggedFunctor VectorVal) rs))
--   runIO :: RelOp c a rs -> IO (Relation (Rec (TaggedFunctor VectorVal)) rs)

-- data Relation (rs :: [(k,*)]) where
--   RelationNull    :: NullRelArity -> Relation '[]
--   RelationPresent :: Rec (TaggedFunctor VectorVal) (r ': rs) -> Relation (r ': rs)

data Relation (a :: [(k,*)] -> *) (rs :: [(k,*)]) where
  RelationNull    :: a '[] -> NullRelArity -> Relation a '[]
  RelationPresent :: a (r ': rs) -> Relation a (r ': rs)

data RelOp (a :: [(k,*)] -> *) (rs :: [(k,*)]) where
  RelTable    :: 
       Rec (DictFun MinimalConstraints) rs
    -> OrdList rs 
    -> Relation a rs 
    -> RelOp a rs
  RelJoin     :: RelOp a as -> RelOp a bs -> RelOp a (Union as bs)
  RelRestrict :: Sublist super sub -> Pred sub -> RelOp a super -> RelOp a super
  RelProject  :: Sublist super sub -> RelOp a super -> RelOp a sub

valEq :: Proxy key -> val -> Pred '[ '(key,val)]
valEq _ v = PredEqValue v

colEq :: (Cmp key1 key2 ~ 'GT)
  => Proxy val -> Proxy key1 -> Proxy key2 -> Pred '[ '(key1,val), '(key2,val)]
colEq _ _ _ = PredEqCols (OrdListCons OrdListSingle)

project :: forall sub subKeys super a. 
     (sub ~ SublistLookupMany super subKeys, ImplicitSublist super sub)
  => Proxy subKeys -> RelOp a super -> RelOp a sub
project _ relOp = RelProject (implicitSublist :: Sublist super sub) relOp

restrict :: ImplicitSublist super sub => Pred sub -> RelOp a super -> RelOp a super
restrict pred relOp = RelRestrict implicitSublist pred relOp

equijoin :: forall a ls rs name1 name2 v.
  ( ImplicitSublist ls '[ '(name1,v)]
  , ImplicitSublist rs '[ '(name2,v)]
  , v ~ SublistLookup rs name2
  )
  => Proxy name1 -> Proxy name2 -> RelOp a ls 
  -> RelOp a rs -> RelOp a (Union ls rs)
equijoin _ _ = equijoinExplicit 
  (implicitSublist :: Sublist ls '[ '(name1,v)])
  (implicitSublist :: Sublist rs '[ '(name2,v)])

equijoinExplicit :: forall ls rs name1 name2 v a.
     Sublist ls '[ '(name1,v)] 
  -> Sublist rs '[ '(name2,v)] 
  -> RelOp a ls -> RelOp a rs -> RelOp a (Union ls rs)
equijoinExplicit subLs subRs ls rs = case (lDict,rDict) of
  (DictFun, DictFun) -> case applyCmpString (proxyFst lDict) (proxyFst rDict) of
    LTy -> error "lt... hmmm"
    GTy -> RelRestrict 
      (unionSublist 
        (relOpNamesTypes ls) 
        (relOpNamesTypes rs) 
        (relOpOrdered ls)
        (relOpOrdered rs)
        subLs subRs
      )
      (PredEqCols (OrdListCons OrdListSingle)) (RelJoin ls rs)
    EQy -> error "hmmm"
  where
  lDict :: DictFun (ConstrainFst TypeString) '(name1,v)
  lDict = case projectRec subLs (relOpTypes ls) of
    d :& RNil -> d
  rDict :: DictFun (ConstrainFst TypeString) '(name2,v)
  rDict = case projectRec subRs (relOpTypes rs) of
    d :& RNil -> d

relOpOrdered :: RelOp a rs -> OrdList rs
relOpOrdered = go
  where
  go :: forall a as. RelOp a as -> OrdList as
  go (RelTable _ asOrd _)      = asOrd
  go (RelRestrict _ _ relNext) = go relNext
  go (RelProject sub relNext)  = ordSublist sub (go relNext)
  go (RelJoin relA relB)       = ordUnion (go relA) (go relB)

relOpConstraints :: RelOp a rs -> Rec (DictFun MinimalConstraints) rs
relOpConstraints = go
  where
  go :: forall a as. RelOp a as -> Rec (DictFun MinimalConstraints) as
  go (RelTable c _ _)          = c -- ordListDict (Proxy :: Proxy (ConstrainFst TypeString :&: ConstrainSnd Typeable :&: ConstrainSnd Ord)) asOrd
  go (RelRestrict _ _ relNext) = go relNext
  go (RelProject sub relNext)  = projectRec sub (go relNext)
  go (RelJoin a b)             = unionRec (go a) (go b)

relOpTypes :: forall a rs. RelOp a rs -> Rec (DictFun (ConstrainFst TypeString)) rs
relOpTypes = id
  . weakenRecDictFun 
      (Proxy :: Proxy (ConstrainFst TypeString))
      (Sub Dict)
  . relOpConstraints

relOpNamesTypes :: forall a rs. RelOp a rs -> Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)) rs
relOpNamesTypes = id
  . weakenRecDictFun 
      (Proxy :: Proxy (ConstrainFst TypeString :&: ConstrainSnd Typeable))
      (Sub Dict)
  . relOpConstraints

relOpOrd :: forall a rs. RelOp a rs -> Rec (DictFun (ConstrainSnd Ord)) rs
relOpOrd = id
  . weakenRecDictFun 
      (Proxy :: Proxy (ConstrainSnd Ord))
      (Sub Dict)
  . relOpConstraints

proxifyRelOp :: RelOp a rs -> Rec Proxy rs
proxifyRelOp = recToProxy . relOpConstraints

nullRelArityToInt :: NullRelArity -> Int
nullRelArityToInt a = case a of
  NullRelOne -> 1
  NullRelZero -> 0

yo :: Int
yo = 4


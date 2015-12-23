{-# LANGUAGE PolyKinds #-}
module Data.Relation where

import Control.Monad
import Data.Set (Set)
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.List.NonEmpty as NonEmpty
import Data.Typeable (Typeable,TypeRep)
import Control.Monad.Trans.Writer.Strict (Writer,tell,runWriter)
import Data.Monoid (Any(..))
import qualified GHC.Prim as Prim
import Data.Vinyl.Named
import GHC.TypeLits (CmpSymbol)
import Data.List.TypeLevel 
import Data.Vector.Vinyl.Default.Types (VectorVal)
import Data.Proxy (Proxy(..))
import Data.Vinyl.Core (Rec(..))
import Data.Vector.Vinyl.TypeLevel
import Data.Constraint

newtype Col = Col { getCol :: String }
  deriving (Eq,Ord)

data UTable = UTable
  { utName    :: String
  , utColumns :: Set Col
  }

data Pred (f :: CmpFun (NamedTypeOf key *) -> *) (rs :: [NamedTypeOf key *]) where
  PredNot     :: Pred f rs -> Pred f rs
  PredOr      :: Sublist cs as -> Sublist cs bs 
              -> Pred f as -> Pred f bs -> Pred f cs
  PredAnd     :: Sublist cs as -> Sublist cs bs
              -> Pred f as -> Pred f bs -> Pred f cs
  PredEqValue :: val -> Pred f '[ 'NamedTypeOf key val]
  PredEqCol   :: OrdList f '[ 'NamedTypeOf key1 val, 'NamedTypeOf key2 val] 
              -> Pred f '[ 'NamedTypeOf key1 val, 'NamedTypeOf key2 val] 

data RelOp (f :: CmpFun (NamedTypeOf key *) -> *) (rs :: [NamedTypeOf key *]) where
  RelTable    :: ListAll rs IsNamedType
              => String
              -> OrdList f rs 
              -> Rec (NamedWith f VectorVal) rs 
              -> RelOp f rs
  RelJoin     :: RelOp f as -> RelOp f bs -> RelOp f (Union f as bs)
  RelRestrict :: Sublist super sub -> Pred f sub -> RelOp f super -> RelOp f super
  RelProject  :: Sublist super sub -> RelOp f super -> RelOp f sub

valEq :: Proxy key -> val -> Pred f '[ 'NamedTypeOf key val]
valEq _ v = PredEqValue v

colEq :: ApplyCmp f ('NamedTypeOf key1 val) ('NamedTypeOf key2 val) ~ GT
  => Proxy val -> Proxy key1 -> Proxy key2 -> Pred f '[ 'NamedTypeOf key1 val, 'NamedTypeOf key2 val]
colEq _ _ _ = PredEqCol (OrdListCons OrdListSingle)

project :: forall sub subKeys super f. 
     (sub ~ SublistLookupMany super subKeys, ImplicitSublist super sub)
  => Proxy subKeys -> RelOp f super -> RelOp f sub
project _ relOp = RelProject (implicitSublist :: Sublist super sub) relOp

restrict :: ImplicitSublist super sub => Pred f sub -> RelOp f super -> RelOp f super
restrict pred relOp = RelRestrict implicitSublist pred relOp

equijoin :: forall f ls rs name1 name2 v.
  ( ImplicitSublist ls '[ 'NamedTypeOf name1 v]
  , ImplicitSublist rs '[ 'NamedTypeOf name2 v]
  , v ~ SublistLookup rs name2
  )
  => Proxy name1 -> Proxy name2 -> RelOp f ls 
  -> RelOp f rs -> RelOp f (Union f ls rs)
equijoin _ _ = equijoinExplicit 
  (implicitSublist :: Sublist ls '[ 'NamedTypeOf name1 v])
  (implicitSublist :: Sublist rs '[ 'NamedTypeOf name2 v])

equijoinExplicit :: forall ls rs name1 name2 v f.
     Sublist ls '[ 'NamedTypeOf name1 v] 
  -> Sublist rs '[ 'NamedTypeOf name2 v] 
  -> RelOp f ls -> RelOp f rs -> RelOp f (Union f ls rs)
equijoinExplicit subLs subRs ls rs = case (lDict,rDict) of
  (DictFun Dict, DictFun Dict) -> case applyCmpString fProxy lDict rDict of
    LTy -> error "lt... hmmm"
    GTy -> RelRestrict 
      (unionSublist fProxy 
        (relOpTypes ls) 
        (relOpTypes rs) 
        (relOpOrdered ls)
        (relOpOrdered rs)
        subLs subRs
      )
      (PredEqCol (OrdListCons OrdListSingle)) (RelJoin ls rs)
    EQy -> error "hmmm"
  where
  fProxy = Proxy :: Proxy f
  lDict :: DictFun IsNamedType ('NamedTypeOf name1 v)
  lDict = case projectRec subLs (relOpTypes ls) of
    d :& RNil -> d
  rDict :: DictFun IsNamedType ('NamedTypeOf name2 v)
  rDict = case projectRec subRs (relOpTypes rs) of
    d :& RNil -> d

relOpOrdered :: forall f rs. RelOp f rs -> OrdList f rs
relOpOrdered = go
  where
  go :: forall g as. RelOp g as -> OrdList g as
  go (RelTable _ asOrd _)        = asOrd
  go (RelRestrict _ _ relNext) = go relNext
  go (RelProject sub relNext)  = ordSublist sub (go relNext)
  go (RelJoin relA relB)       = ordUnion (go relA) (go relB)

relOpTypes :: forall f rs. RelOp f rs -> Rec (DictFun IsNamedType) rs
relOpTypes = go
  where
  go :: forall g as. RelOp g as -> Rec (DictFun IsNamedType) as
  go (RelTable _ asOrd _)      = ordListDict (Proxy :: Proxy IsNamedType) asOrd
  go (RelRestrict _ _ relNext) = go relNext
  go (RelProject sub relNext)  = projectRec sub (go relNext)
  go (RelJoin a b)             = unionRec (Proxy :: Proxy g) (go a) (go b)

toUnchecked :: forall f rs. RelOp f rs -> URelOp
toUnchecked = go
  where
  go :: forall g as. RelOp g as -> URelOp
  go (RelTable name asOrd _) = URelTable 
    (UTable name (colsFromRec (ordListDict (Proxy :: Proxy IsNamedType) asOrd)))
  go (RelJoin a b) = URelJoin (go a) (go b)
  go (RelProject sub relNext) = URelProject 
    (colsFromRec (projectRec sub (relOpTypes relNext))) (go relNext)
  go (RelRestrict sub pred relNext) = URelRestrict 
    (predToUnchecked (projectRec sub (relOpTypes relNext)) pred) 
    (go relNext)

colsFromRec :: Rec (DictFun IsNamedType) rs -> Set Col
colsFromRec RNil = Set.empty
colsFromRec (r@(DictFun Dict) :& rs) = Set.insert (Col (ntName r)) (colsFromRec rs)

data UPred
  = UPredEqValue Col TypeRep Prim.Any -- like Dynamic
  | UPredEqCols  Col   Col
  | UPredAnd     UPred UPred
  | UPredOr      UPred UPred
  | UPredNot     UPred

data URelOp
  = URelProject (Set Col) URelOp
  | URelJoin URelOp URelOp 
  | URelRestrict UPred URelOp 
  | URelTable UTable

-- predOrdList :: Pred f rs -> OrdList f rs
-- predOrdList = go
--   where
--   go :: forall f rs. Pred f rs -> OrdList f rs
--   go (PredEqCol o) = o
--   go (PredEqValue _) = OrdListSingle
  
predToUnchecked :: Rec (DictFun IsNamedType) rs -> Pred f rs -> UPred
predToUnchecked = go
  where
  go :: forall f rs. Rec (DictFun IsNamedType) rs -> Pred f rs -> UPred
  go d (PredNot p)       = UPredNot (go d p)
  go d pred@(PredAnd subA subB a b) = UPredAnd
    (go (projectRec subA d) a)
    (go (projectRec subB d) b)
  go d pred@(PredOr subA subB a b) = UPredOr
    (go (projectRec subA d) a)
    (go (projectRec subB d) b)
  go (d@(DictFun Dict) :& e@(DictFun Dict) :& RNil) (PredEqCol (OrdListCons OrdListSingle)) = 
    UPredEqCols (Col (ntName d)) (Col (ntName e))
  go (d@(DictFun Dict) :& RNil) (PredEqValue v) = 
    UPredEqValue (Col (ntName d)) (ntType d) (toAny v)

showURelOp :: URelOp -> String
showURelOp = go 0
  where 
  go :: Int -> URelOp -> String
  go i (URelTable ut) = List.replicate i ' ' ++ utName ut
    ++ " (" ++ join (List.intersperse "," (map getCol $ Set.toList (utColumns ut))) ++ ")" ++ "\n"
  go i (URelJoin a b) = List.replicate i ' ' ++ "Natural Join" ++ "\n" ++ go (i + 2) a ++ go (i + 2) b
  go i (URelProject cols r) = List.replicate i ' ' 
    ++ "Project (" ++ join (List.intersperse "," (map getCol $ Set.toList cols)) ++ ")" ++ "\n" ++ go (i + 2) r 
  go i (URelRestrict pred r) = List.replicate i ' ' 
    ++ "Restrict (" ++ showUPred pred ++ ")" ++ "\n" ++ go (i + 2) r 

showUPred :: UPred -> String
showUPred = go
  where
  go (UPredNot pred) = "¬ ( " ++ go pred ++ ")"
  go (UPredAnd a b) = "( " ++ go a ++ " ) ∧ ( " ++ go b ++ ")"
  go (UPredOr a b) = "( " ++ go a ++ " ) ∨ ( " ++ go b ++ ")"
  go (UPredEqCols a b) = getCol a ++ " = " ++ getCol b
  go (UPredEqValue col _ v) = getCol col ++ " = ?"

-- This should bring a URelOp to a canonical form. This 
-- involves pushing any restrictions as far down as
-- they can go and collapsing them when possible. This
-- function should be idempotent.
canonizeURelOp :: URelOp -> URelOp
canonizeURelOp op = if changed then canonizeURelOp opNext else opNext
  where
  (opNext,Any changed) = runWriter (canonizeURelOpStep op)

canonizeURelOpStep :: URelOp -> Writer Any URelOp
canonizeURelOpStep = go
  where
  go u@(URelTable a) = return u
  -- Don't push natural join into anything 
  go (URelJoin op1 op2) = URelJoin <$> go op1 <*> go op2
  go (URelProject cols opNext) = case opNext of
    URelTable a -> return (URelProject cols opNext)
    URelProject colsSuper op -> do
      when (not (cols `Set.isSubsetOf` colsSuper))
        $ error "canonizeURelOp: URelProject incorrect scenario"
      tell (Any True) 
      return (URelProject cols op)
    -- To ensure termination, we do not allow projection
    -- to be pushed inside of restriction.
    URelRestrict pred op -> do
      canonizedRel <- go (URelRestrict pred op)
      return (URelProject cols canonizedRel)
    URelJoin op1 op2 -> do
      let op1Cols = uRelOpCols op1
          op2Cols = uRelOpCols op2
          joinCols = Set.intersection op1Cols op2Cols
          op1' = URelProject (Set.intersection (uRelOpCols op1) cols) op1
          op2' = URelProject (Set.intersection (uRelOpCols op2) cols) op2
      if joinCols `Set.isSubsetOf` cols
        then do
          tell (Any True)
          return (URelJoin op1' op2')
        else fmap (URelProject cols) (go (URelJoin op1 op2))
  go (URelRestrict pred opNext) = case opNext of
    URelTable a -> return (URelRestrict pred opNext)
    URelProject projCols op -> do
      let predCols = uPredCols pred
      when (not (predCols `Set.isSubsetOf` projCols))
        $ error "canonizeURelOp: URelRestrict incorrect scenario"
      tell (Any True) 
      return (URelProject projCols (URelRestrict pred op))
    URelRestrict predNext op -> do
      tell (Any True)
      return (URelRestrict (UPredAnd pred predNext) op)
    URelJoin op1 op2 -> do
      let (pred1, pred2, predPostJoin) = uPredSplitForJoin pred (uRelOpCols op1) (uRelOpCols op2)
          op1' = case pred1 of
            [] -> op1
            p : ps -> URelRestrict (uPredMergeAnd (p :| ps)) op1
          op2' = case pred2 of
            [] -> op2
            p : ps -> URelRestrict (uPredMergeAnd (p :| ps)) op2
          opJoin = URelJoin op1' op2'
          opJoinRestrict = case predPostJoin of
            [] -> opJoin
            p : ps -> URelRestrict (uPredMergeAnd (p :| ps)) opJoin
      when (List.length pred1 > 0 || List.length pred2 > 0) $ tell (Any True)
      return opJoinRestrict

-- The resulting UPreds cannot be UPredAnd. Also, I should
-- use Data.List.NonEmpty. Also, the UPred needs to be
-- in conjunctive normal form before passing it to this
-- function. The resulting list must have at least one
-- element.
--
-- TODO: Force everything into conjunctive normal form first
--
uPredSplitAnd :: UPred -> NonEmpty UPred
uPredSplitAnd = go
  where
  go (UPredAnd x y) = nonEmptyAppend (go x) (go y)
  go p = p :| []

uPredMergeAnd :: NonEmpty UPred -> UPred
uPredMergeAnd = nonEmptyFoldl1 UPredAnd 

nonEmptyAppend :: NonEmpty a -> NonEmpty a -> NonEmpty a
nonEmptyAppend (a :| as) (b :| bs) = a :| (as ++ [b] ++ bs)

nonEmptyFoldl1 :: (a -> a -> a) -> NonEmpty a -> a
nonEmptyFoldl1 g (a :| as) = List.foldl g a as

-- Split up a predicate into two parts. The first is the
-- subpredicates that contain the columns passed in. The
-- second is the subpredicates that don't.
uPredSplitForJoin :: UPred -> Set Col -> Set Col -> ([UPred],[UPred],[UPred])
uPredSplitForJoin masterPred cols1 cols2 = 
  flip foldMap (NonEmpty.toList (uPredSplitAnd masterPred)) $ \pred -> 
    let predCols = uPredCols pred
        isSub1 = predCols `Set.isSubsetOf` cols1
        isSub2 = predCols `Set.isSubsetOf` cols2
    in case (isSub1, isSub2) of
      (True , True ) -> ([pred],[pred],[])
      (True , False) -> ([pred],[],[])
      (False, True ) -> ([],[pred],[])
      (False, False) -> ([],[],[pred])

uPredCols :: UPred -> Set Col
uPredCols = go
  where
  go (UPredEqValue a _ _) = Set.singleton a
  go (UPredEqCols a b)    = Set.fromList [a,b]
  go (UPredAnd x y)       = Set.union (uPredCols x) (uPredCols y)
  go (UPredOr x y)        = Set.union (uPredCols x) (uPredCols y)
  go (UPredNot x)         = uPredCols x 

uRelOpCols :: URelOp -> Set Col
uRelOpCols = go
  where
  go (URelTable t)        = utColumns t
  go (URelProject cols _) = cols
  go (URelRestrict _ op)  = go op
  go (URelJoin op1 op2)   = Set.union (go op1) (go op2)

type family RequiredEqStar (a :: *) (b :: *) (r :: k) :: k where
  RequiredEqStar a a k = k

-- data OrdNamedTypes (cs :: [NamedType *]) where
--   OrdNamedTypesNil    :: OrdNamedTypes '[]
--   OrdNamedTypesSingle :: Proxy c -> OrdNamedTypes '[c]
--   OrdNamedTypesAppend :: 
--     ( CmpSymbol cname dname ~ GT
--     )
--     => Proxy ('NamedType cname cval) 
--     -> OrdNamedTypes (('NamedType dname dval) ': cs) 
--     -> OrdNamedTypes (('NamedType cname cval) ': ('NamedType dname dval) ': cs)


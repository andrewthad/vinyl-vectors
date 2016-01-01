{-# LANGUAGE PolyKinds #-}
module Data.Relation where

import Control.Monad
import Data.Set (Set)
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Vector.Vinyl.Default.NonEmpty.Monomorphic as R
import Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Join (indexManyPredicate)
import Data.Typeable (Typeable,TypeRep,typeRep)
import Control.Monad.Trans.Writer.Strict (Writer,tell,runWriter)
import Data.Monoid (Any(..))
import qualified GHC.Prim as Prim
import Data.Vinyl.Named
import GHC.TypeLits (CmpSymbol)
import Data.List.TypeLevel 
import Data.Vector.Vinyl.Default.Types (VectorVal(..))
import Data.Proxy (Proxy(..))
import Data.Vinyl.Core (Rec(..))
import Data.List.TypeLevel
import Data.Constraint
import qualified Data.Graph.Inductive.Tree as Patricia
-- import qualified Data.Graph.Inductive.PatriciaTree as Patricia
import qualified Data.Graph.Inductive.Graph as Graph
import Control.Monad.Trans.State
import Control.Arrow (first, second)
import Data.Map (Map)
import Data.Vector.Vinyl.Default.Types (HasDefaultVector)
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector.Generic as G
import qualified Data.Map.Strict as Map
import Unsafe.Coerce (unsafeCoerce)

newtype Col = Col { getCol :: String }
  deriving (Eq,Ord,Show)
data NullRelArity = NullRelOne | NullRelZero

data UTable = UTable
  { utName    :: String
  , utColumns :: Set Col
  , utData    :: Either NullRelArity (Map Col HiddenVector)
  }

data Relation (rs :: [(k,*)]) where
  RelationNull    :: NullRelArity -> Relation '[]
  RelationPresent :: Rec (UncurriedTaggedFunctor VectorVal) (r ': rs) -> Relation (r ': rs)

relationToUnsafeRelation :: ( ListAll rs RelOpConstraints )
  => Relation rs -> Either NullRelArity (Map Col HiddenVector)
relationToUnsafeRelation r = case r of
  RelationNull a -> Left a
  RelationPresent vrec -> 
    fmap (Map.mapKeys Col) (Right (recToHiddenVectorMap vrec))

data Pred (rs :: [(k,*)]) where
  PredNot     :: Pred rs -> Pred rs
  PredOr      :: Sublist cs as -> Sublist cs bs 
              -> Pred as -> Pred bs -> Pred cs
  PredAnd     :: Sublist cs as -> Sublist cs bs
              -> Pred as -> Pred bs -> Pred cs
  PredEqValue :: val -> Pred '[ '(key,val)]
  PredEqCols  :: OrdList '[ '(key1,val), '(key2,val)] 
              -> Pred '[ '(key1,val), '(key2,val)] 


data RelOp (rs :: [(k,*)]) where
  RelTable    :: 
    ( ListAll rs RelOpConstraints 
    -- , ListAll rs (ConstrainFst TypeString)
    -- , ListAll rs (ConstrainSnd Typeable)
    -- , ListAll rs (ConstrainSnd HasDefaultVector)
    -- , ListAll rs (ConstrainSnd Ord)
    )
    => String
    -> OrdList rs 
    -> Relation rs 
    -> RelOp rs
  RelJoin     :: RelOp as -> RelOp bs -> RelOp (Union as bs)
  RelRestrict :: Sublist super sub -> Pred sub -> RelOp super -> RelOp super
  RelProject  :: Sublist super sub -> RelOp super -> RelOp sub

valEq :: Proxy key -> val -> Pred '[ '(key,val)]
valEq _ v = PredEqValue v

colEq :: Cmp key1 key2 ~ GT
  => Proxy val -> Proxy key1 -> Proxy key2 -> Pred '[ '(key1,val), '(key2,val)]
colEq _ _ _ = PredEqCols (OrdListCons OrdListSingle)

project :: forall sub subKeys super. 
     (sub ~ SublistLookupMany super subKeys, ImplicitSublist super sub)
  => Proxy subKeys -> RelOp super -> RelOp sub
project _ relOp = RelProject (implicitSublist :: Sublist super sub) relOp

restrict :: ImplicitSublist super sub => Pred sub -> RelOp super -> RelOp super
restrict pred relOp = RelRestrict implicitSublist pred relOp

equijoin :: forall ls rs name1 name2 v.
  ( ImplicitSublist ls '[ '(name1,v)]
  , ImplicitSublist rs '[ '(name2,v)]
  , v ~ SublistLookup rs name2
  )
  => Proxy name1 -> Proxy name2 -> RelOp ls 
  -> RelOp rs -> RelOp (Union ls rs)
equijoin _ _ = equijoinExplicit 
  (implicitSublist :: Sublist ls '[ '(name1,v)])
  (implicitSublist :: Sublist rs '[ '(name2,v)])

equijoinExplicit :: forall ls rs name1 name2 v.
     Sublist ls '[ '(name1,v)] 
  -> Sublist rs '[ '(name2,v)] 
  -> RelOp ls -> RelOp rs -> RelOp (Union ls rs)
equijoinExplicit subLs subRs ls rs = case (lDict,rDict) of
  (DictFun Dict, DictFun Dict) -> case applyCmpString (proxyFst lDict) (proxyFst rDict) of
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

relOpOrdered :: forall rs. RelOp rs -> OrdList rs
relOpOrdered = go
  where
  go :: forall as. RelOp as -> OrdList as
  go (RelTable _ asOrd _)      = asOrd
  go (RelRestrict _ _ relNext) = go relNext
  go (RelProject sub relNext)  = ordSublist sub (go relNext)
  go (RelJoin relA relB)       = ordUnion (go relA) (go relB)

relOpConstraints :: forall rs. RelOp rs -> Rec (DictFun RelOpConstraints) rs
relOpConstraints = go
  where
  go :: forall as. RelOp as -> Rec (DictFun RelOpConstraints) as
  go (RelTable _ asOrd _)      = ordListDict (Proxy :: Proxy RelOpConstraints) asOrd
  go (RelRestrict _ _ relNext) = go relNext
  go (RelProject sub relNext)  = projectRec sub (go relNext)
  go (RelJoin a b)             = unionRec (go a) (go b)

relOpTypes :: forall rs. RelOp rs -> Rec (DictFun (ConstrainFst TypeString)) rs
relOpTypes = id
  . weakenRecDictFun 
      (Proxy :: Proxy (ConstrainFst TypeString))
      (Sub Dict)
  . relOpConstraints

relOpNamesTypes :: forall rs. RelOp rs -> Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)) rs
relOpNamesTypes = id
  . weakenRecDictFun 
      (Proxy :: Proxy (ConstrainFst TypeString :&: ConstrainSnd Typeable))
      (Sub Dict)
  . relOpConstraints


  -- where
  -- go :: forall as. RelOp as -> Rec (DictFun (ConstrainSnd Typeable)) as
  -- go (RelTable _ asOrd _)      = ordListDict (Proxy :: Proxy (ConstrainSnd Typeable)) asOrd
  -- go (RelRestrict _ _ relNext) = go relNext
  -- go (RelProject sub relNext)  = projectRec sub (go relNext)
  -- go (RelJoin a b)             = unionRec (go a) (go b)

toUnchecked :: forall rs. RelOp rs -> URelOp
toUnchecked = go
  where
  go :: forall as. RelOp as -> URelOp
  go (RelTable name asOrd relation) = URelTable 
    (UTable 
      name 
      (colsFromRec $ weakenRecDictFun 
        (Proxy :: Proxy (ConstrainFst TypeString)) 
        (Sub Dict)
        (ordListDict (Proxy :: Proxy RelOpConstraints) asOrd)
      )
      (relationToUnsafeRelation relation)
    )
  go (RelJoin a b) = URelJoin (go a) (go b)
  go (RelProject sub relNext) = URelProject 
    (colsFromRec (projectRec sub (relOpTypes relNext))) (go relNext)
  go (RelRestrict sub pred relNext) = URelRestrict 
    (predToUnchecked (projectRec sub (relOpNamesTypes relNext)) pred) 
    (go relNext)

colsFromRec :: Rec (DictFun (ConstrainFst TypeString)) rs -> Set Col
colsFromRec RNil = Set.empty
colsFromRec (r@(DictFun Dict) :& rs) = Set.insert (Col (typeString $ proxyFst r)) (colsFromRec rs)

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
  | URelJoinMany (Patricia.Gr URelOp (Col,Col))

instance Show URelOp where
  show = showURelOp

-- predOrdList :: Pred f rs -> OrdList f rs
-- predOrdList = go
--   where
--   go :: forall f rs. Pred f rs -> OrdList f rs
--   go (PredEqCols o) = o
--   go (PredEqValue _) = OrdListSingle
  
predToUnchecked :: Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)) rs -> Pred rs -> UPred
predToUnchecked = go
  where
  go :: forall f rs. Rec (DictFun (ConstrainFst TypeString :&: ConstrainSnd Typeable)) rs -> Pred rs -> UPred
  go d (PredNot p)       = UPredNot (go d p)
  go d pred@(PredAnd subA subB a b) = UPredAnd
    (go (projectRec subA d) a)
    (go (projectRec subB d) b)
  go d pred@(PredOr subA subB a b) = UPredOr
    (go (projectRec subA d) a)
    (go (projectRec subB d) b)
  go (d@(DictFun Dict) :& e@(DictFun Dict) :& RNil) (PredEqCols (OrdListCons OrdListSingle)) = 
    UPredEqCols (Col (typeString $ proxyFst d)) (Col (typeString $ proxyFst e))
  go (d@(DictFun Dict) :& RNil) (PredEqValue v) = 
    UPredEqValue (Col (typeString $ proxyFst d)) (typeRep $ proxySnd d) (toAny v)

toAny :: a -> Prim.Any
toAny = unsafeCoerce

-- Improve this at some point to tab things over correctly on a 
-- multi join.
showURelOp :: URelOp -> String
showURelOp = go 0
  where 
  go :: Int -> URelOp -> String
  go i (URelTable ut) = List.replicate i ' ' 
    ++ "Table: " ++ utName ut
    ++ " (" ++ join (List.intersperse ", " (map getCol $ Set.toList (utColumns ut))) ++ ")" ++ "\n"
  go i (URelJoin a b) = List.replicate i ' ' ++ "Natural Join" ++ "\n" ++ go (i + 2) a ++ go (i + 2) b
  go i (URelProject cols r) = List.replicate i ' ' 
    ++ "Project (" ++ join (List.intersperse "," (map getCol $ Set.toList cols)) ++ ")" ++ "\n" ++ go (i + 2) r 
  go i (URelRestrict pred r) = List.replicate i ' ' 
    ++ "Restrict (" ++ showUPred pred ++ ")" ++ "\n" ++ go (i + 2) r 
  go i (URelJoinMany gr) = List.replicate i ' '
    ++ "Join Many\n" ++ List.replicate (i + 2) ' ' ++ "( " ++ join 
       ( List.intersperse ("\n" ++ List.replicate (i + 2) ' ' ++ ", ")
         ( map (\(n1,n2,(c1,c2)) -> "[" ++ show n1 ++ "," ++ show n2 ++ "] " ++ getCol c1 ++ " = " ++ getCol c2) 
               (Graph.labEdges gr) 
         )
       )
    ++ "\n" ++ List.replicate (i + 2) ' ' ++ ")\n" 
    ++ join (map (\(n,u) -> replicate (i + 2) ' ' ++ show n ++ ". " ++ drop (i + 5) (go (i + 5) u)) (Graph.labNodes gr))

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

uPredGraphJoins :: URelOp -> URelOp
uPredGraphJoins = go
  where
  go :: URelOp -> URelOp
  go (URelTable a) = URelTable a
  go (URelProject cols a) = URelProject cols (go a)
  go (URelJoinMany _) = error "uPredGraphJoins: URelJoinMany encountered"
  go u@(URelJoin a b) = URelJoinMany (makeGraph (execState (build u) mempty))
  go (URelRestrict pred (URelJoin a b)) = error "write this"
  go (URelRestrict pred a) = URelRestrict pred (go a)
  build :: URelOp -> State ([(Col,Col)],[URelOp]) ()
  build (URelTable a) = modify (second (URelTable a :))
  build (URelProject cols a) = modify (second (URelProject cols (go a) :))
  build (URelJoin a b) = do
    mapM_ (\col -> modify (first ((col,col):)))
      (Set.toList (Set.intersection (uRelOpCols a) (uRelOpCols b)))
    build a
    build b
  build (URelJoinMany _) = error "uPredGraphJoins: URelJoinMany encountered"
  build (URelRestrict pred (URelJoin a b)) = do
    -- TODO: Figure out a better story for OR predicates.
    -- Right now, it just errors.
    let preds = NonEmpty.toList (uPredSplitAnd pred)
        colPairs = map requireEqCol preds
    modify (first (colPairs ++))
    build (URelJoin a b)
  build (URelRestrict pred a) = modify (second (URelRestrict pred (go a) :))

-- partial function
requireEqCol :: UPred -> (Col,Col)
requireEqCol (UPredEqCols a b) = (a,b)
requireEqCol _ = error "requireEqCol failed"

-- The predicates passed to this function should be list
-- of predication that should be ANDed together. None of 
-- them should be UPredAnd or UPredEqValue.
makeGraph :: ([(Col,Col)],[URelOp]) -> Patricia.Gr URelOp (Col,Col)
makeGraph (preds,ops) = List.foldl' goEdge initGraph preds
  where 
  goEdge graph (c1,c2) = 
    List.foldl' 
      (\g (n1,n2) -> Graph.insEdge (n1,n2,(c1,c2)) 
                   . Graph.delLEdge (n1,n2,(c1,c2))
                   $ g) 
      graph $ do
        ix1 <- colBaseTableIxs c1
        ix2 <- colBaseTableIxs c2
        when (c1 == c2) $ guard (ix1 > ix2)
        return (ix1,ix2)
  initGraph = Graph.mkGraph ixedOps []
  ixedOps  = zip (enumFrom 1) ops
  ixedCols :: [(Int, Set Col)]
  ixedCols = map (second uRelOpCols) ixedOps
  colBaseTableIxs col = id
    $ map fst
    $ flip List.filter ixedCols $ \(ix,cols) -> 
        Set.member col cols

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

proxifyRelOp :: RelOp rs -> Rec Proxy rs
proxifyRelOp = error "write me"

relOpRun :: forall rs. 
  ( ListAll rs (ConstrainFst TypeString)
  , ListAll rs (ConstrainSnd Typeable)
  , ListAll rs (ConstrainSnd HasDefaultVector)
  )
  => RelOp rs 
  -> Rec (UncurriedTaggedFunctor VectorVal) rs
relOpRun r = id
  (indexedHiddenVectorMapsToRec
    (proxifyRelOp r)
    .
    fmap (second $ Map.mapKeys getCol)
  )
  . either (const []) id
  . uRelOpRun
  . toUnchecked
  $ r

-- Runs the URelOp without first optimizing the AST.
uRelOpRun :: URelOp -> Either NullRelArity [(U.Vector Int, Map Col HiddenVector)]
uRelOpRun = go
  where
  go (URelTable t) = case utData t of
    Left a -> Left a
    Right m -> case Map.elems m of
      HiddenVector (VectorVal v) : _ -> Right [(U.fromList (enumFromTo 0 (G.length v - 1)),m)]
      [] -> error "uRelOpRun: URelTable with incorrect empty map"
  go (URelRestrict pred op) = case go op of
    -- Left case is unlikely. The predicate must be a lambda
    -- that is effectively `const True` or `const False`.
    Left a -> case a of
      NullRelZero -> Left NullRelZero
      NullRelOne -> error "uRelOpRun: fix me after lambdas are allowed"
    Right xs -> 
      let mask = applyUPred pred (listMapHelper xs)
      in Right (map (first (U.ifilter (\i _ -> mask U.! i))) xs)

-- This could be optimized more
applyUPred :: UPred -> Map Col (U.Vector Int, HiddenVector) -> U.Vector Bool
applyUPred upred m = go upred
  where
  go (UPredEqValue col rep val) = case Map.lookup col m of
    Nothing -> error ("applyUPred: column " ++ getCol col ++ " not found.")
    Just (ixs, HiddenVector (VectorVal v)) -> if typeRep v == rep
      then indexManyPredicate (== unsafeCoerce val) ixs v
      else error "applyUPred: mismatched types for UPredEqValue"

-- This assumes that keys are not reused across
-- different maps in the list.
listMapHelper :: Ord k => [(a,Map k v)] -> Map k (a,v)
listMapHelper = Map.unions . map (\(a,m) -> fmap (\v -> (a,v)) m)


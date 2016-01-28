{-# LANGUAGE PolyKinds #-}
module Data.Relation.Run.Basic
  ( runTest
  , fromTest
  ) where

import           Control.Arrow                                              (first, second)
import           Control.Monad
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Writer.Strict                          (Writer, runWriter, tell)
import           Data.Constraint
import           Data.Foldable
import qualified Data.Graph.Inductive.Graph                                 as Graph
import qualified Data.Graph.Inductive.Tree                                  as Patricia
import qualified Data.List                                                  as List
import           Data.List.NonEmpty                                         (NonEmpty ((:|)))
import qualified Data.List.NonEmpty                                         as NonEmpty
import           Data.List.TypeLevel
import           Data.List.TypeLevel.Constraint
import qualified Data.List.TypeLevel.Union                                  as Union
import           Data.List.TypeLevel.Witness
import           Data.Map                                                   (Map)
import qualified Data.Map.Strict                                            as Map
import           Data.Monoid                                                (Any (..))
import           Data.Monoid
import           Data.Proxy                                                 (KProxy (..), Proxy (..))
import           Data.Relation
import           Data.Relation.Backend                                      (Basic (..), BasicInner (..), Common (..), NullRelArity (..), Test (..), nullRelArityToInt)
import           Data.Set                                                   (Set)
import qualified Data.Set                                                   as Set
import           Data.Tagged.Functor                                        (TaggedFunctor (..))
import           Data.Tuple.TypeLevel
import           Data.Type.Equality
import           Data.Typeable                                              (TypeRep, Typeable, typeRep)
import           Data.TypeString
import           Data.Vec
import qualified Data.Vector.Generic                                        as G
import qualified Data.Vector.Hybrid                                         as Hybrid
import qualified Data.Vector.Hybrid.Internal                                as Hybrid
import qualified Data.Vector.Unboxed                                        as U
import qualified Data.Vector.Vec.Internal                                   as VV
import qualified Data.Vector.Vinyl.Default.NonEmpty.Monomorphic             as R
import           Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Implication (listAllVector)
import qualified Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Internal    as R
import           Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Join        (indexMany, indexManyPredicate, matchingIndicesExtraImmutable, sortWithIndices)
import qualified Data.Vector.Vinyl.Default.NonEmpty.Tagged                  as VT
import qualified Data.Vector.Vinyl.Default.NonEmpty.Tagged.Implication      as VT
import           Data.Vector.Vinyl.Default.Types                            (VectorVal (..))
import           Data.Vector.Vinyl.Default.Types                            (HasDefaultVector)
import           Data.Vinyl.Class.Implication                               (eqTRec, listAllOrd, listAllToRecAll)
import           Data.Vinyl.Core                                            hiding (Dict)
import           Data.Vinyl.DictFun
import           Data.Vinyl.Functor                                         (Compose (..), Identity)
import           Data.Vinyl.Named
import           Debug.Trace                                                (traceShowId)
import qualified GHC.Prim                                                   as Prim
import           GHC.TypeLits                                               (CmpSymbol)
import           Unsafe.Coerce                                              (unsafeCoerce)
-- import qualified Data.Graph.Inductive.PatriciaTree as Patricia

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
  | URelBinary BinOp URelOp URelOp
  | URelRename Col Col URelOp

runTest :: RelOp Basic rs -> IO (Test rs)
runTest r = return $ case runOptimized r of
  CommonNull a -> case a of
    NullRelZero -> Test []
    NullRelOne -> Test [RNil]
  CommonPresent rs -> let c = basicRelOpConstraints r in
    case dictFunToListAll $ weakenRecDictFun (Proxy :: Proxy (ConstrainSnd HasDefaultVector)) (Sub Dict) c of
      Dict -> case VT.listAllVector c of
        Sub Dict -> Test $ VT.toList $ VT.fromRec rs

fromTest :: forall r rs. (RecApplicative (r ': rs), ListAll (r ': rs) ExtraConstraints)
  => Test (r ': rs) -> Common BasicInner (r ': rs)
fromTest t = case dictFunToListAll (weakenRecDictFun (Proxy :: Proxy (ConstrainSnd HasDefaultVector)) (Sub Dict) c) of
  Dict -> case VT.listAllVector (head $ getTest t) of
    Sub Dict -> id
     . CommonPresent
     . BasicInner c
     . VT.toRec
     . VT.fromList
     . getTest
     $ t
  where
  c :: Rec (DictFun ExtraConstraints) (r ': rs)
  c = reifyDictFun (Proxy :: Proxy ExtraConstraints) (rpure Proxy)

type ExtraConstraints =
      ConstrainSnd HasDefaultVector
  :&: ConstrainSnd Show

-- data R (rs :: [(k,*)]) = R
--   String -- name of table
--   (Rec (DictFun (ConstrainSnd HasDefaultVector :&: ConstrainSnd Show)) rs) -- extra constraints
--   (Rec (TaggedFunctor VectorVal) rs) -- value

newtype UResult = UResult
  { getUResult :: Either NullRelArity (NonEmpty (U.Vector Int, Map Col HiddenVector)) }

instance Show UResult where
  show (UResult e) = "UResult:\n" ++ case e of
    Left a -> show a
    Right xs -> List.unlines $ join
      [ NonEmpty.toList $ fmap (("  " ++) . show . fst) xs
      , NonEmpty.toList $ fmap (showMap . snd) xs
      ]
    where showMap m = join $ flip map (Map.toList m) $ \(Col name, hv) ->
            "  " ++ name ++ ":\n" ++
            "    " ++ show hv ++ "\n"
newtype Col = Col { getCol :: String }
  deriving (Eq,Ord,Show)

relationName :: Basic rs -> String
relationName (Basic name _) = name

combineConstraints :: Rec (DictFun MinimalConstraints) rs
  -> Rec (DictFun ExtraConstraints) rs -> Rec (DictFun RelOpConstraints) rs
combineConstraints RNil RNil = RNil
combineConstraints (DictFun :& as) (DictFun :& bs) = DictFun :& combineConstraints as bs

relationToUnsafeRelation :: Rec (DictFun MinimalConstraints) rs
  -> Basic rs -> Either NullRelArity (Map Col HiddenVector)
relationToUnsafeRelation minimal (Basic _ r) = case r of
  CommonNull a -> Left a
  CommonPresent (BasicInner extra vrec) -> case recDictFunToDict (combineConstraints minimal extra) of
    Dict -> fmap (Map.mapKeys Col) (Right (recToHiddenVectorMap vrec))

uResultColumns :: UResult -> NonEmpty (U.Vector Int, Map Col HiddenVector)
uResultColumns (UResult (Right x)) = x
uResultColumns (UResult (Left _)) =
  error "uResultColumns: called on UResult with no columns"

data UTable = UTable
  { utName    :: !String
  , utColumns :: !(Set Col)
  , utData    :: !(Either NullRelArity (Map Col HiddenVector))
  }

-- partial function
requireEqCol :: UPred -> Maybe (Col,Col)
requireEqCol (UPredEqCols a b) = Just (a,b)
requireEqCol _ = Nothing

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

nonEmptyFromList :: String -> [a] -> NonEmpty a
nonEmptyFromList err [] = error err
nonEmptyFromList _ (a:as) = a :| as

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
      let op1Cols  = uRelOpCols op1
          op2Cols  = uRelOpCols op2
          joinCols = Set.intersection op1Cols op2Cols
          op1'     = URelProject (Set.intersection (uRelOpCols op1) cols) op1
          op2'     = URelProject (Set.intersection (uRelOpCols op2) cols) op2
      if joinCols `Set.isSubsetOf` cols
        then do
          tell (Any True)
          return (URelJoin op1' op2')
        else fmap (URelProject cols) (go (URelJoin op1 op2))
    -- Redo both of these later to make more optimal
    URelRename _ _ _ -> URelProject cols <$> go opNext
    URelBinary _ _ _ -> URelProject cols <$> go opNext
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
    -- Redo both of these later to make more optimal
    URelRename _ _ _ -> URelRestrict pred <$> go opNext
    URelBinary _ _ _ -> URelRestrict pred <$> go opNext
  go (URelBinary binOp op1 op2) = URelBinary binOp <$> go op1 <*> go op2
  -- Redo this. We actually want to push renames all the way to
  -- the bottom.
  go (URelRename old new op) = URelRename old new <$> go op

uPredGraphJoins :: URelOp -> URelOp
uPredGraphJoins = go
  where
  go :: URelOp -> URelOp
  go (URelTable a) = URelTable a
  go (URelProject cols a) = URelProject cols (go a)
  go (URelJoinMany _) = error "uPredGraphJoins: URelJoinMany encountered"
  go u@(URelJoin a b) = URelJoinMany (makeGraph (execState (build u) mempty))
  -- go (URelRestrict pred (URelJoin a b)) = error "restriction on top on join: write this"
  -- This will currently do an equijoin wrong. We need to add back the
  -- other pattern.
  go (URelRestrict pred a) = URelRestrict pred (go a)
  go (URelBinary binOp a b) = URelBinary binOp (go a) (go b)
  go (URelRename old new a) = URelRename old new (go a)
  build :: URelOp -> State ([(Col,Col)],[URelOp]) ()
  build (URelTable a) = modify (second (URelTable a :))
  build (URelBinary binOp a b) = modify (second (URelBinary binOp (go a) (go b) :))
  build (URelRename old new a) = modify (second (URelRename old new (go a) :))
  build (URelProject cols a) = modify (second (URelProject cols (go a) :))
  build (URelJoin a b) = do
    mapM_ (\col -> modify (first ((col,col):)))
      (Set.toList (Set.intersection (uRelOpCols a) (uRelOpCols b)))
    build a
    build b
  build (URelJoinMany _) = error "uPredGraphJoins: URelJoinMany encountered"
  build (URelRestrict pred (URelJoin a b)) = do
    let preds = NonEmpty.toList (uPredSplitAnd pred)
    case mapM requireEqCol preds of
      Just colPairs -> do
        modify (first (colPairs ++))
        build (URelJoin a b)
      Nothing -> modify (second (URelRestrict pred (go (URelJoin a b)) :))
  build (URelRestrict pred a) = modify (second (URelRestrict pred (go a) :))

toUnchecked :: forall rs. RelOp Basic rs -> URelOp
toUnchecked = go
  where
  go :: forall as. RelOp Basic as -> URelOp
  go (RelTable dicts asOrd relation) = URelTable
    (UTable
      (relationName relation)
      (colsFromRec $ weakenRecDictFun
        (Proxy :: Proxy (ConstrainFst TypeString))
        (Sub Dict)
        dicts
      )
      (relationToUnsafeRelation dicts relation)
    )
  go (RelJoin a b) = URelJoin (go a) (go b)
  go (RelProject sub relNext) = URelProject
    (colsFromRec (projectRec sub (relOpTypes relNext))) (go relNext)
  go (RelRestrict sub pred relNext) = URelRestrict
    (predToUnchecked (projectRec sub (relOpNamesTypes relNext)) pred)
    (go relNext)
  go (RelBinary binOp a b) = URelBinary binOp (go a) (go b)

colsFromRec :: Rec (DictFun (ConstrainFst TypeString)) rs -> Set Col
colsFromRec RNil = Set.empty
colsFromRec (r@DictFun :& rs) = Set.insert (Col (typeString $ proxyFst r)) (colsFromRec rs)

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
  go (d@DictFun :& e@DictFun :& RNil) (PredEqCols (OrdListCons OrdListSingle)) =
    UPredEqCols (Col (typeString $ proxyFst d)) (Col (typeString $ proxyFst e))
  go (d@DictFun :& RNil) (PredEqValue v) =
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
  go (UPredNot pred)        = "¬ ( " ++ go pred ++ ")"
  go (UPredAnd a b)         = "( " ++ go a ++ " ) ∧ ( " ++ go b ++ ")"
  go (UPredOr a b)          = "( " ++ go a ++ " ) ∨ ( " ++ go b ++ ")"
  go (UPredEqCols a b)      = getCol a ++ "                            = " ++ getCol b
  go (UPredEqValue col _ v) = getCol col ++ "                          = ?"

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
  go (URelJoinMany g)     = Set.unions (map (go . snd) (Graph.labNodes g))

relOpRun :: forall (rs :: [(a,*)]) (k :: KProxy a).
  ( ListAll rs (ConstrainFst TypeString)
  , ListAll rs (ConstrainSnd Typeable)
  , ListAll rs (ConstrainSnd HasDefaultVector)
  , k ~ 'KProxy
  )
  => RelOp Basic rs
  -> VT.Vector k (Rec (TaggedFunctor Identity) rs)
relOpRun r = id
  . VT.fromRec
  . (indexedHiddenVectorMapsToRec
      (proxifyRelOp r)
      .
      fmap (second $ Map.mapKeys getCol)
    )
  . NonEmpty.toList
  . uResultColumns
  . uRelOpRun
  . uPredGraphJoins
  . canonizeURelOp
  . toUnchecked
  $ r

runOptimized :: RelOp Basic rs -> Common (Rec (TaggedFunctor VectorVal)) rs
runOptimized r =
  case (ctxTypeable,ctxTypeString,ctxVector) of
    (Dict,Dict,Dict) -> case (e,proxifyRelOp r) of
      (Left a, RNil) -> CommonNull a
      (Left _, _ :& _) -> error "runOptimized: impossible"
      (Right vs, p@(_ :& _)) -> id
        . CommonPresent
        . (indexedHiddenVectorMapsToRec p .  fmap (second $ Map.mapKeys getCol))
        . NonEmpty.toList
        $ vs
      (Right _, RNil) -> error "runOptimized: impossible"
  where
  UResult e = uRelOpRun . uPredGraphJoins . canonizeURelOp . toUnchecked $ r
  ctxBasic = basicRelOpConstraints r
  ctxPlain = relOpConstraints r
  ctxTypeable = dictFunToListAll $ weakenRecDictFun (Proxy :: Proxy (ConstrainSnd Typeable)) (Sub Dict) ctxPlain
  ctxTypeString = dictFunToListAll $ weakenRecDictFun (Proxy :: Proxy (ConstrainFst TypeString)) (Sub Dict) ctxPlain
  ctxVector = dictFunToListAll $ weakenRecDictFun (Proxy :: Proxy (ConstrainSnd HasDefaultVector)) (Sub Dict) ctxBasic

-- Runs the URelOp without first optimizing the AST. You should
-- make sure that uPredGraphJoins has already been called on the
-- URelOp before running this.
uRelOpRun :: URelOp -> UResult
uRelOpRun = go
  where
  go :: URelOp -> UResult
  go (URelTable t) = case utData t of
    Left a -> UResult $ Left a
    Right m -> case Map.elems m of
      HiddenVector (VectorVal v) : _ -> UResult
        $ Right $ (U.fromList (enumFromTo 0 (G.length v - 1)),m) :| []
      [] -> error "uRelOpRun: URelTable with incorrect empty map"
  go (URelRestrict pred op) = case go op of
    -- Left case is unlikely. The predicate must be a lambda
    -- that is effectively `const True` or `const False`.
    UResult (Left a) -> case a of
      NullRelZero -> UResult (Left NullRelZero)
      NullRelOne -> error "uRelOpRun: fix me after lambdas are allowed"
    UResult (Right xs) ->
      let mask = applyUPred pred (listMapHelper (NonEmpty.toList xs))
      in UResult (Right (fmap (first (U.ifilter (\i _ -> mask U.! i))) xs))
  go (URelProject cols op) = case go op of
    UResult (Left a) -> if Set.size cols == 0
      then UResult (Left a)
      else error "uRelOpRun: projecting non existent columns"
    UResult (Right xs@((ixs, _) :| _))
      | Set.null cols -> (UResult . Left) (if U.length ixs > 0 then NullRelOne else NullRelZero)
      | allCols == cols -> UResult (Right xs)
      -- The otherwise clause is currently wrong. It would be
      -- right if one of the columns being projected were
      -- a candidate key.
      -- | otherwise       -> UResult $ Right $ fmap
      --     (second $ Map.filterWithKey (\k _ -> Set.member k cols)) xs
      | otherwise -> deduplicate remainingVals
      where
      allCols = Set.fromList $ join $ NonEmpty.toList $ fmap (Map.keys . snd) xs
      remainingVals :: [(Col, (U.Vector Int, HiddenVector))]
      remainingVals = id
        $ join
        $ fmap (\(ixs,m) -> map (\(k,h) -> (k,(ixs,h))) $ Map.toList m)
        $ NonEmpty.toList
        $ fmap (second $ Map.filterWithKey (\k _ -> Set.member k cols)) xs
  go (URelJoin _ _) =
    error "uRelOpRun: URelJoin should already have been replaced"
  go (URelJoinMany graph) = let
    nodes = Graph.labNodes graph
    graphResults = Graph.nmap go graph
    in performJoins graphResults
  -- This can be made much more efficient if we know about dependencies
  -- within the relation.
  go (URelBinary binOp op1 op2) = case (getUResult (go op1),getUResult (go op2)) of
    (Left a1, Left a2) -> UResult $ Left $ case binOp of
      BinOpUnion        -> if a1 == NullRelOne || a2 == NullRelOne then NullRelOne else NullRelZero
      BinOpIntersection -> if a1 == NullRelOne && a2 == NullRelOne then NullRelOne else NullRelZero
      BinOpSubtraction  -> if a1 == NullRelOne && a2 == NullRelZero then NullRelOne else NullRelZero
    (Right xs1, Right xs2) -> UResult $ Right $ case binOp of
      BinOpUnion -> let
        m1 = flattenVectorMap (NonEmpty.toList xs1)
        m2 = flattenVectorMap (NonEmpty.toList xs2)
        in error "uehotn"
      _ -> error "uRelOpRun: write binary operations other than union"
    (_,_) -> error "uRelOpRun: binary incorrect situation happened"
  go (URelRename old new op) = case go op of
    UResult (Left _) -> error "uRelOpRun: cannot call rename on 0 column relation"
    UResult (Right xs) -> UResult . Right $ fmap (second $ Map.mapKeys replaceOld) xs
    where
    replaceOld :: Col -> Col
    replaceOld c = if c == old then new else c

flattenVectorMap :: [(U.Vector Int,Map Col HiddenVector)] -> [(Col,(U.Vector Int, HiddenVector))]
flattenVectorMap = join . fmap (\(ixs,m) -> map (\(k,h) -> (k,(ixs,h))) $ Map.toList m)

deduplicate :: [(Col,(U.Vector Int, HiddenVector))] -> UResult
deduplicate xs = let
  keys  = fmap fst xs
  pairs = fmap snd xs
  hvs1  = nonEmptyFromList "uRelOpRun: expected non empty list"
        $ flattenIndexedHiddenVectors pairs
  hrec  = removeDuplicates $ nonEmptyHiddenVectorsToHiddenRec hvs1
  hvs2@(hvs2Head :| _) = hiddenRecToNonEmptyHiddenVectors hrec
  newIxs = case hvs2Head of
    HiddenVector (VectorVal v) -> U.enumFromN 0 (G.length v)
  res = ((newIxs, Map.fromList $ uncheckedZip keys (NonEmpty.toList hvs2)) :| [])
  in UResult $ Right res

performJoins :: Patricia.Gr UResult (Col,Col) -> UResult
performJoins = go
  where
  go graphResults = let
    results = Graph.labNodes graphResults
    graphArities = Graph.nmap uRelArity graphResults
    arities = Graph.labNodes graphArities
    getResult node = case List.lookup node results of
      Nothing -> error "uRelOpRun: graph error"
      Just a -> a
    getArity node = case List.lookup node arities of
      Nothing -> error "uRelOpRun: graph error"
      Just a -> a
    -- This will currently break if a cross join is attempted
    edgeLists = labEdgeLists graphResults
    in case edgeLists of
      [] -> case results of
        []        -> error "performJoins: no nodes"
        [(_,r)]   -> r
        a : b : _ -> error "still need to support cross join"
      (_ : _) -> let
        ((n1,n2),colPairs) = List.minimumBy (\((a1,b1),_) ((a2,b2),_) ->
          compare (getArity a1 * getArity b1) (getArity a2 * getArity b2))
          edgeLists
        r1 = getResult n1
        r2 = getResult n2
        rnew = joinUResultsOn r1 r2 colPairs
        gnew = mergeNodes rnew n1 n2 graphResults
        in go gnew

-- The new node will take on the id of the first node.
mergeNodes :: a -> Graph.Node -> Graph.Node -> Patricia.Gr a b -> Patricia.Gr a b
mergeNodes a n1 n2 g = let
  adj1  = filter ((/= n2) . snd) $ Graph.lneighbors g n1
  adj2  = filter ((/= n1) . snd) $ Graph.lneighbors g n2
  enew  = map (\(pair,n) -> (n1,n,pair)) (adj1 ++ adj2)
  -- adj2' = map (second (const n1)) adj2
  e1    = map (\n -> (n1,n)) $ Graph.neighbors g n1
  e2    = map (\n -> (n2,n)) $ Graph.neighbors g n2
  in Graph.insEdges enew $ Graph.insNode (n1,a) $ Graph.delNodes [n1,n2] $ Graph.delEdges (e1 ++ e2) $ g

crossJoinUResults :: UResult -> UResult -> UResult
crossJoinUResults = error "write cross join"

-- goals:
--   1. Group the indices on both sides
--   2. Sort the join columns (along with all indices)

indexManyHidden :: U.Vector Int -> HiddenVector -> HiddenVector
indexManyHidden ixs (HiddenVector (VectorVal a)) = HiddenVector (VectorVal (indexMany ixs a))

joinUResultsOn :: UResult -> UResult -> NonEmpty (Col,Col) -> UResult
joinUResultsOn (UResult e1) (UResult e2) pairs = case (e1,e2) of
  (Left a, _) -> error "joinUResultsOn: zero attr relation given"
  (_, Left a) -> error "joinUResultsOn: zero attr relation given"
  (Right v1, Right v2) -> let
    m1 = listMapHelper (NonEmpty.toList v1)
    hr1 = nonEmptyHiddenVectorsToHiddenRec (NonEmpty.map (uncurry indexManyHidden . unJust . flip Map.lookup m1 . fst) pairs)
    ixs1 = nonEmptyToVec (fmap fst v1)
    m2 = listMapHelper (NonEmpty.toList v2)
    hr2 = nonEmptyHiddenVectorsToHiddenRec (NonEmpty.map (uncurry indexManyHidden . unJust . flip Map.lookup m2 . fst) pairs)
    ixs2 = nonEmptyToVec (fmap fst v2)
    res :: UResult
    res = case hr1 of
      NonEmptyHiddenRec hr1_ -> case ixs1 of
        SomeNonEmptyVec ixs1_ -> case listAllOrd (Proxy :: Proxy Identity) hr1_ (Sub Dict) of
          Sub Dict -> case listAllVector hr1_ of
            Sub Dict -> case hr2 of
              NonEmptyHiddenRec hr2_ -> case ixs2 of
                SomeNonEmptyVec ixs2_ -> case listAllOrd (Proxy :: Proxy Identity) hr2_ (Sub Dict) of
                  Sub Dict -> case eqTRec hr1_ hr2_ of
                    Nothing -> error "joinUResultsOn: mismatched column types"
                    Just Refl -> case listAllToRecAll (Proxy :: Proxy Show) (Proxy :: Proxy Identity) hr1_ (Sub Dict) of
                      Sub Dict -> case listAllToRecAll (Proxy :: Proxy Show) (Proxy :: Proxy Identity) hr2_ (Sub Dict) of
                        Sub Dict -> let
                          s1 = Hybrid.modify sortWithIndices (Hybrid.V (VV.V ixs1_) (R.V hr1_))
                          s2 = Hybrid.modify sortWithIndices (Hybrid.V (VV.V ixs2_) (R.V hr2_))
                          natJoinCols = map fst $ filter (\(a,b) -> a == b) $ NonEmpty.toList pairs
                          rmNatJoinExtraCols m = foldl' (\a b -> removeFirstHelper b a) m natJoinCols
                          in case matchingIndicesExtraImmutable s1 s2 of
                              (Hybrid.V (VV.V newIxs1) (VV.V newIxs2)) ->
                                UResult $ Right $ rmNatJoinExtraCols $ uncheckedZipNonEmpty
                                  (nonEmptyAppend
                                    (vecToNonEmpty newIxs1)
                                    (vecToNonEmpty newIxs2)
                                  )
                                  ( nonEmptyAppend
                                    (fmap snd v1)
                                    (fmap snd v2)
                                  )

    in res
  where
  unJust Nothing  = error "joinUResultsOn: key lookup failure"
  unJust (Just a) = a

uncheckedZipNonEmpty :: NonEmpty a -> NonEmpty b -> NonEmpty (a,b)
uncheckedZipNonEmpty (a :| as) (b :| bs) = (a,b) :| uncheckedZip as bs

uncheckedZip :: [a] -> [b] -> [(a,b)]
uncheckedZip [] (_:_) = error "uncheckedZip: mismatch"
uncheckedZip (_:_) [] = error "uncheckedZip: mismatch"
uncheckedZip [] [] = []
uncheckedZip (a : as) (b : bs) = (a,b) : uncheckedZip as bs

zeroUResult :: UResult -> UResult
zeroUResult = error "zeroUResult: write this"

uRelArity :: UResult -> Int
uRelArity (UResult r) = case r of
  Left a -> nullRelArityToInt a
  Right ((ixs,_) :| _) -> U.length ixs

labEdgeLists :: Patricia.Gr a b -> [((Graph.Node,Graph.Node),NonEmpty b)]
labEdgeLists = id
  . Map.toList
  . Map.fromListWith nonEmptyAppend
  . map (\(a,b,c) -> ((a,b),c :| []))
  . Graph.labEdges

-- This could be optimized more
applyUPred :: UPred -> Map Col (U.Vector Int, HiddenVector) -> U.Vector Bool
applyUPred upred m = go upred
  where
  go (UPredEqValue col rep val) = case Map.lookup col m of
    Nothing -> error ("applyUPred: column " ++ getCol col ++ " not found.")
    Just (ixs, HiddenVector (VectorVal v)) -> if typeRep v == rep
      then indexManyPredicate (== unsafeCoerce val) ixs v
      else error "applyUPred: mismatched types for UPredEqValue"
  go (UPredOr a b) = U.zipWith (||) (go a) (go b)


removeFirstHelper :: Ord k => k -> NonEmpty (a,Map k v) -> NonEmpty (a,Map k v)
removeFirstHelper k xs = case removeFirstHelperList k (NonEmpty.toList xs) of
  [] -> error "removeFirstHelper: invariant violated"
  a : as -> a :| as

removeFirstHelperList :: Ord k => k -> [(a,Map k v)] -> [(a,Map k v)]
removeFirstHelperList _ [] = error "removeFirstHelper: key not found"
removeFirstHelperList k ((a,m) : xs) = case Map.lookup k m of
  Nothing -> (a,m) : removeFirstHelperList k xs
  Just v -> let m' = Map.delete k m in
    if Map.null m' then xs else (a,m') : xs

-- This assumes that keys are not reused across
-- different maps in the list.
listMapHelper :: Ord k => [(a,Map k v)] -> Map k (a,v)
listMapHelper = Map.unionsWith (\_ _ -> error "listMapHelper: duplicate field") . map (\(a,m) -> fmap (\v -> (a,v)) m)

basicRelOpConstraints :: RelOp Basic rs -> Rec (DictFun ExtraConstraints) rs
basicRelOpConstraints = go
  where
  go :: forall as. RelOp Basic as -> Rec (DictFun ExtraConstraints) as
  go (RelTable _ _ (Basic _ (CommonNull _))) = RNil
  go (RelTable _ _ (Basic _ (CommonPresent (BasicInner c _)))) = c
  go (RelRestrict _ _ relNext) = go relNext
  go (RelProject sub relNext)  = projectRec sub (go relNext)
  go (RelJoin a b)             = Union.rec
    (weakenRecDictFun2 (Sub Dict) $ relOpConstraints a)
    (weakenRecDictFun2 (Sub Dict) $ relOpConstraints b)
    (go a) (go b)
  go (RelBinary _ a _)         = go a


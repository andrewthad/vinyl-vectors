module Main where

import           Test.Relation

import           Data.Monoid                                             (mempty)
import           Test.Framework                                          (defaultMain, defaultMainWithOpts, testGroup)
import           Test.Framework.Options                                  (TestOptions, TestOptions' (..))
import           Test.Framework.Providers.HUnit
import           Test.Framework.Providers.QuickCheck2                    (testProperty)
import           Test.Framework.Runners.Options                          (RunnerOptions, RunnerOptions' (..))
import qualified Test.QuickCheck.Property                                as Property

import           Test.HUnit
import           Test.QuickCheck

import           Control.Exception                                       (SomeException (..))
import           Control.Monad.ST                                        (ST,
                                                                          runST)
import           Data.List
import           Data.Proxy                                              (Proxy (Proxy), asProxyTypeOf)
import qualified Data.Vector                                             as Vector
import qualified Data.Vector.Hybrid                                      as Hybrid
import qualified Data.Vector.Unboxed                                     as Unboxed
import qualified Data.Vector.Vinyl.Default.NonEmpty.Monomorphic          as Vinyl
import qualified Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Internal as Vinyl
import           Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Join     (fullJoinIndices, fullJoinIndicesNaive)
import           Data.Vector.Vinyl.Default.Types                         (VectorVal)

import           Data.Relation.Backend                                   as Backend
import qualified Data.Relation.Run.Naive                                 as Naive
import qualified Data.Set                                                as Set
import           Data.Vinyl.Arbitrary                                    (ArbitraryRec (..))
import           Data.Vinyl.Core                                         (Rec (..), rtraverse)
import           Data.Vinyl.Functor                                      (Compose (..), Identity (..))
import qualified Data.Vinyl.Named                                        as Named
import           Test.Relation

main = do
  putStrLn ""
  defaultMain tests

tests =
  [ testGroup "Correctness of Algorithms"
    [ testProperty "Full Join Indices" correctFullJoinIndices
    ]
  , testGroup "Relational Operations - Naive"
    $ relationSpecTests Naive.runTest
       $ ListToRelation (Backend.Naive . Set.fromList . Backend.getTest)
      :& ListToRelation (Backend.Naive . Set.fromList . Backend.getTest)
      :& ListToRelation (Backend.Naive . Set.fromList . Backend.getTest)
      :& RNil
  ]

correctFullJoinIndices :: [Int] -> [Int] -> Property.Result
correctFullJoinIndices as bs = if actual == expected
  then Property.succeeded
  else Property.failed
    { Property.reason = unlines
      [ "Correct result:   " ++ show expected
      , "Algorithm result: " ++ show actual
      ]
    }
  where
  expected = sort (fullJoinIndicesNaive as bs)
  actual   = sort (vectorImplementationResult)
  p        = Proxy :: Proxy (Hybrid.Vector Unboxed.Vector Unboxed.Vector (Int, Int))
  vectorImplementationResult = Hybrid.toList $ flip asProxyTypeOf p $ runST $ return
    =<< Hybrid.freeze
    =<<
    ( do a <- Vector.thaw (Vector.fromList as)
         b <- Vector.thaw (Vector.fromList bs)
         fullJoinIndices a b
    )

-- composedNamedRecordIdentity :: (Maybe Int,Maybe String,Maybe Double) -> Bool
-- composedNamedRecordIdentity (ints,strings,doubles) =
--   toRecs r ==
--   toRecs ((Named.composedFromDynamicMap r . Named.composedToDynamicMap) r)
--   where
--   r = Compose (fmap withAge ints)
--    :& Compose (fmap withName strings)
--    :& Compose (fmap withSpeed doubles)
--    :& RNil
--   withAge x = NamedValue x :: NamedValue ('NamedType "age" Int)
--   withName x = NamedValue x :: NamedValue ('NamedType "name" String)
--   withSpeed x = NamedValue x :: NamedValue ('NamedType "speed" Double)
--   toRecs :: Rec (Compose Maybe NamedValue) rs -> Maybe (Rec NamedValue rs)
--   toRecs = rtraverse (\(Compose xs) -> xs)

-- namedVectorRecordIdentity :: [(Int,Bool)] -> Bool
-- namedVectorRecordIdentity xs =
--   namedVecs ==
--   Named.hiddenVectorMapToRec namedVecs (Named.recToHiddenVectorMap namedVecs)
--   where
--   namedVecs = Named.zipNames (Proxy :: Proxy '["age","living"]) vecRecs
--   vecRecs :: Rec VectorVal '[Int,Bool]
--   vecRecs = case Vinyl.fromList (map (\(i,b) -> Identity i :& Identity b :& RNil) xs) of
--     Vinyl.V v -> v
--
-- namedRecordIdentity :: ArbitraryRec NamedValue
--   '[ 'NamedType "age" Int
--    , 'NamedType "name" String
--    , 'NamedType "active" Bool
--    , 'NamedType "speed" Double
--    ] -> Bool
-- namedRecordIdentity (ArbitraryRec r) =
--   r == (Named.fromDynamicMap r . Named.toDynamicMap) r

-- , testGroup "Unsafe Named Record Operations"
--   [ testProperty "To and from forms identity" namedRecordIdentity
--   , testProperty "To and from composed variants form identity" composedNamedRecordIdentity
--   , testProperty "To and from named vector forms identity" namedVectorRecordIdentity
--   ]

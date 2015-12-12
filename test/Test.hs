module Main where

import Data.Monoid (mempty)
import Test.Framework (defaultMain, defaultMainWithOpts, testGroup)
import Test.Framework.Options (TestOptions, TestOptions'(..))
import Test.Framework.Runners.Options (RunnerOptions, RunnerOptions'(..))
import Test.Framework.Providers.HUnit
import Test.Framework.Providers.QuickCheck2 (testProperty)
import qualified Test.QuickCheck.Property as Property

import Test.QuickCheck
import Test.HUnit

import Data.List
import qualified Data.Vector as Vector
import qualified Data.Vector.Hybrid as Hybrid
import qualified Data.Vector.Unboxed as Unboxed
import Data.Vector.Vinyl.Default.Types (VectorVal)
import Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Join (fullJoinIndicesNaive,fullJoinIndices)
import qualified Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Internal as Vinyl
import qualified Data.Vector.Vinyl.Default.NonEmpty.Monomorphic as Vinyl
import Control.Monad.ST (ST, runST)
import Data.Proxy (asProxyTypeOf, Proxy(Proxy))
import Control.Exception (SomeException(..))

import Data.Vinyl.Core (Rec(..),rtraverse)
import qualified Data.Vinyl.Named as Named
import Data.Vinyl.Named (NamedValue(..), NamedType(..))
import Data.Vinyl.Arbitrary (ArbitraryRec(..))
import Data.Vinyl.Functor (Identity(..),Compose(..))

main = do
  putStrLn ""
  defaultMain tests

tests = 
  [ testGroup "Correctness of Algorithms" 
    [ testProperty "Full Join Indices" correctFullJoinIndices
    ]
  , testGroup "Unsafe Named Record Operations"
    [ testProperty "To and from forms identity" namedRecordIdentity
    , testProperty "To and from composed variants form identity" composedNamedRecordIdentity
    , testProperty "To and from named vector forms identity" namedVectorRecordIdentity
    ]
  ]

namedVectorRecordIdentity :: [(Int,Bool)] -> Bool
namedVectorRecordIdentity xs = 
  namedVecs == 
  Named.hiddenVectorMapToRec namedVecs (Named.recToHiddenVectorMap namedVecs)
  where
  namedVecs = Named.zipNames (Proxy :: Proxy '["age","living"]) vecRecs 
  vecRecs :: Rec VectorVal '[Int,Bool]
  vecRecs = case Vinyl.fromList (map (\(i,b) -> Identity i :& Identity b :& RNil) xs) of
    Vinyl.V v -> v

composedNamedRecordIdentity :: (Maybe Int,Maybe String,Maybe Double) -> Bool
composedNamedRecordIdentity (ints,strings,doubles) =
  toRecs r == 
  toRecs ((Named.composedFromDynamicMap r . Named.composedToDynamicMap) r)
  where 
  r = Compose (fmap withAge ints) 
   :& Compose (fmap withName strings) 
   :& Compose (fmap withSpeed doubles) 
   :& RNil
  withAge x = NamedValue x :: NamedValue ('NamedType "age" Int)
  withName x = NamedValue x :: NamedValue ('NamedType "name" String)
  withSpeed x = NamedValue x :: NamedValue ('NamedType "speed" Double)
  toRecs :: Rec (Compose Maybe NamedValue) rs -> Maybe (Rec NamedValue rs)
  toRecs = rtraverse (\(Compose xs) -> xs)

namedRecordIdentity :: ArbitraryRec NamedValue 
  '[ 'NamedType "age" Int
   , 'NamedType "name" String
   , 'NamedType "active" Bool
   , 'NamedType "speed" Double
   ] -> Bool
namedRecordIdentity (ArbitraryRec r) = 
  r == (Named.fromDynamicMap r . Named.toDynamicMap) r

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
  actual = sort (vectorImplementationResult)
  p = Proxy :: Proxy (Hybrid.Vector Unboxed.Vector Unboxed.Vector (Int, Int))
  vectorImplementationResult = Hybrid.toList $ flip asProxyTypeOf p $ runST $ return
    =<< Hybrid.freeze
    =<< 
    ( do a <- Vector.thaw (Vector.fromList as) 
         b <- Vector.thaw (Vector.fromList bs) 
         fullJoinIndices a b
    )


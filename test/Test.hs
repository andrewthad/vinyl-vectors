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
import Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Join (fullJoinIndicesNaive,fullJoinIndices)
import Control.Monad.ST (ST, runST)
import Data.Proxy (asProxyTypeOf, Proxy(Proxy))
import Control.Exception (SomeException(..))

main = do
  putStrLn ""
  defaultMain tests

tests = 
  [ testGroup "Correctness of Algorithms" 
    [ testProperty "Full Join Indices" correctFullJoinIndices
    ]
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
  expected = fullJoinIndicesNaive as bs
  actual = vectorImplementationResult
  p = Proxy :: Proxy (Hybrid.Vector Unboxed.Vector Unboxed.Vector (Int, Int))
  vectorImplementationResult = Hybrid.toList $ flip asProxyTypeOf p $ runST $ return
    =<< Hybrid.freeze
    =<< 
    ( do a <- Vector.thaw (Vector.fromList as) 
         b <- Vector.thaw (Vector.fromList bs) 
         fullJoinIndices a b
    )


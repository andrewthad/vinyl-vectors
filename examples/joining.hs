{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
import qualified Data.Vector.Unboxed as U
import qualified Data.Vector as V
import qualified Data.Vector.Hybrid  as Hybrid
import Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Join (fullJoinIndices)
import Data.Text (Text)

main :: IO ()
main = do
  -- Numbers Example
  a <- U.thaw (multiplesOf 3)
  b <- U.thaw (multiplesOf 5)

  printHeading "Sorted Numbers 1"
  U.mapM_ print =<< U.freeze a

  printHeading "Sorted Numbers 2"
  U.mapM_ print =<< U.freeze b

  printHeading "Matching Indices of Numbers"
  f <- Hybrid.freeze =<< fullJoinIndices a b
  let _ = asTypeOf f (undefined :: Hybrid.Vector U.Vector U.Vector (Int,Int))
  _ <- Hybrid.mapM_ (\x -> print x >> return x) f

  -- Names example
  a <- V.thaw names1
  b <- V.thaw names2

  printHeading "Unsorted Names 1"
  V.mapM_ print =<< V.freeze a

  printHeading "Unsorted Names 2"
  V.mapM_ print =<< V.freeze b

  printHeading "Matching Indices of Names"
  f <- Hybrid.freeze =<< fullJoinIndices a b
  let _ = asTypeOf f (undefined :: Hybrid.Vector U.Vector U.Vector (Int,Int))
  _ <- Hybrid.mapM_ (\x -> print x >> return x) f
  return ()

names1 :: V.Vector Text
names1 = V.fromList ["Drew","Luke","Alexa","Amber","Jake","Drew","Josh"]

names2 :: V.Vector Text
names2 = V.fromList ["Alexa","Alexa","Drew","Luke","Alexa"]

maxNumber :: Int
maxNumber = 20

multiplesOf :: Int -> U.Vector Int
multiplesOf n = U.fromList (enumFromThenTo 0 n maxNumber)

printHeading :: String -> IO ()
printHeading s = do
  putStrLn "-------------------"
  putStrLn s
  putStrLn "-------------------"


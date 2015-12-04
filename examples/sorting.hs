{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
import Data.Vinyl
import Data.Vinyl.TypeLevel (RIndex,RecAll)
import Data.Vinyl.Functor (Identity(..))
import Data.Text (Text)
import GHC.Exts (Constraint)
import Data.Proxy (Proxy(Proxy))
import Lens.Micro ((^.))
import Data.Vector.Vinyl.TypeLevel (ListAll)
import qualified Data.Vector.Vinyl.Default as V
import qualified Data.Vector.Algorithms.Intro as Intro
import qualified Data.Vector.Algorithms.Merge as Merge

-------------------------------------------------------------------------------
-- This is a simple example of what can be done with vinyl-vectors. If you have
-- already cloned the repository, you can run this example with:
--
--   stack build --flag vinyl-vectors:examples && stack exec sorting
--
-- In this example, we build a vector of records. Internally, this is stored
-- as a structure of arrays. We then use the vector-algorithms to sort the
-- data by several different criteria.

numberOfElements :: Int
numberOfElements = 20

main :: IO ()
main = do
  -- vector-algoritms only works on mutable vectors,
  -- so we just continually mutate recs throughout
  -- the example.
  recs <- V.thaw exampleVectorData 
  printHeading "Original Data"
  V.mapM_ print =<< V.freeze recs

  Merge.sortBy (compareRecOn (Proxy :: Proxy '[Int])) recs
  printHeading "Sort by Number"
  V.mapM_ print =<< V.freeze recs

  Merge.sortBy (compareRecOn (Proxy :: Proxy '[Char])) recs
  printHeading "Sort by Letter"
  V.mapM_ print =<< V.freeze recs

  Merge.sortBy (compareRecOn (Proxy :: Proxy '[Char,Int])) recs
  printHeading "Sort by Letter, Then by Number"
  V.mapM_ print =<< V.freeze recs

type family RElemAll (rs :: [k]) (ts :: [k]) :: Constraint where
  RElemAll rs '[] = ()
  RElemAll rs (t ': ts) = (RElem t rs (RIndex t rs), RElemAll rs ts)

compareRecOn :: forall rs ts. (RElemAll rs ts, ListAll ts Ord, RecApplicative ts)
  => Proxy ts -> Rec Identity rs -> Rec Identity rs -> Ordering
compareRecOn _ a b = compareRecOnExplicit rpureX a b
  where
  rpureX :: Rec Proxy ts
  rpureX = rpure Proxy 

compareRecOnExplicit :: (RElemAll rs ts, ListAll ts Ord)
  => Rec proxy ts -> Rec Identity rs -> Rec Identity rs -> Ordering
compareRecOnExplicit RNil _ _ = LT -- arbitrary, could be GT as well
compareRecOnExplicit (r :& rs) a b = mappend
  (compare (getIdentity $ a ^. rlens r) (getIdentity $ b ^. rlens r))
  (compareRecOnExplicit rs a b)
  

proxyInt = Proxy :: Proxy Int
proxyChar = Proxy :: Proxy Char
proxyText = Proxy :: Proxy Text

exampleVectorData :: V.Vector (Rec Identity '[Int, Char, Text])
exampleVectorData = V.fromList exampleData

exampleData :: [Rec Identity '[Int, Char, Text]]
exampleData = take numberOfElements $ zipWith3 
  (\i c t -> Identity i :& Identity c :& Identity t :& RNil)
  numbers letters names

letters :: [Char]
letters = scramble (cycle (enumFromTo 'a' 'f'))

numbers :: [Int]
numbers = scramble (enumFrom 1)

names :: [Text]
names = cycle
  ["Drew","Luke","Alexa","Fido","Carlos","Juan"
  ,"Anderson","Shen","Anders", "Andy","Jake"
  ,"Josh","Michelle"
  ]

scramble :: [a] -> [a]
scramble [] = []
scramble (a : b : c : xs) = c : b : a : scramble xs
scramble xs = xs

printHeading :: String -> IO ()
printHeading s = do
  putStrLn "-------------------"
  putStrLn s
  putStrLn "-------------------"


{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE QuasiQuotes #-}
import Data.Relation
import Data.Vinyl hiding (Dict)
import Data.Vinyl.Named
import Data.List.TypeLevel
import Data.Text (Text)
import qualified Data.Vector.Generic as G
import Data.Vector.Vinyl.Default.Types (HasDefaultVector, VectorVal(..))
import Data.Proxy
import Data.Constraint
import Data.List.TypeLevel (ListAll)
import Data.Proxy.TH
import Data.Vinyl.Random
import Control.Monad
import System.Random (mkStdGen)
import Data.Vinyl.Functor (Identity)
import Data.Tagged.Functor
import qualified Data.Vector.Vinyl.Default.NonEmpty.Tagged as VT

main :: IO ()
main = do
  putStrLn $ showURelOp $ toUnchecked chosenOp
  putStrLn $ showURelOp $ canonizeURelOp $ toUnchecked chosenOp
  putStrLn $ showURelOp $ uPredGraphJoins $ canonizeURelOp $ toUnchecked chosenOp
  putStrLn dashes
  putStrLn "Dogs Table"
  VT.mapM_ (putStrLn . showSymbolTaggedRec) (VT.fromRec dogsData)
  putStrLn dashes
  putStrLn "People Table"
  VT.mapM_ (putStrLn . showSymbolTaggedRec) (VT.fromRec peopleData)
  putStrLn dashes
  putStrLn "Query Results"
  VT.mapM_ (putStrLn . showSymbolTaggedRec) (relOpRun chosenOp)
  where dashes = "------------------"

-- chosenOp :: URelOp
chosenOp = myOp4

myOp :: URelOp
myOp = toUnchecked 
  $ project [pr|"person_name","person_id"|]
  $ restrict (valEq [pr1|"dog_age"|] (44 :: Int))
  $ RelJoin dogs people

myOp2 :: URelOp
myOp2 = toUnchecked 
  $ restrict (valEq [pr1|"dog_age"|] (44 :: Int))
  $ restrict (valEq [pr1|"dog_name"|] ("Scruff" :: Text))
  $ RelJoin details
  $ RelJoin toy
  $ RelJoin household
  $ equijoin [pr1|"person_id"|] [pr1|"dog_owner"|] people 
  $ dogs2

myOp3 :: RelOp Dog
myOp3 = id
  $ restrict (valEq [pr1|"person_id"|] (1006 :: Int))
  $ dogs

myOp4 :: RelOp (Union (Union Dog Person) Household)
myOp4 = id
  $ restrict (valEq [pr1|"household_name"|] ("Souterrain" :: Text))
  $ RelJoin myOp3
  $ RelJoin household
  $ people

type Dog = 
  '[ '("person_id", Int)
   , '("dog_name", Text)
   , '("dog_age", Int)
   ]

type Person = 
  '[ '("person_weight", Int)
   , '("person_name", Text)
   , '("person_id", Int)
   , '("household_id", Int)
   ]

dogs :: RelOp Dog
dogs = RelTable "dogs" implicitOrdList (RelationPresent dogsData)

dogsData :: Rec (TaggedFunctor VectorVal) Dog
dogsData = VT.toRec $ VT.fromList $ evalRandomData 
  (replicateM 14 (rtraverseIdentityTagged randDog)) 
  (mkStdGen 42)

randDog :: Rec (TaggedFunctor RandomData) Dog
randDog = 
     tagFunctor [pr1|"person_id"|] (intBetween 1000 1007)
  :& tagFunctor [pr1|"dog_name"|]  americanMaleGivenName
  :& tagFunctor [pr1|"dog_age"|]   (intBetween 1 16)
  :& RNil

people :: RelOp Person
people = RelTable "people" implicitOrdList (RelationPresent peopleData)

peopleData :: Rec (TaggedFunctor VectorVal) Person
peopleData = VT.toRec $ VT.fromList $ evalRandomData 
  (replicateM 4 (rtraverseIdentityTagged randPerson)) 
  (mkStdGen 42)

randPerson :: Rec (TaggedFunctor RandomData) Person
randPerson = 
     tagFunctor [pr1|"person_weight"|] (intBetween 120 260)
  :& tagFunctor [pr1|"person_name"|]   americanMaleGivenName
  :& tagFunctor [pr1|"person_id"|]     (intBetween 1000 1009)
  :& tagFunctor [pr1|"household_id"|]  (intBetween 5000 5010)
  :& RNil

type Household = 
  '[ '("household_name", Text)
   , '("household_id", Int)
   ]

household :: RelOp Household
household = RelTable "household" implicitOrdList (RelationPresent householdData)

householdData :: Rec (TaggedFunctor VectorVal) Household
householdData = VT.toRec $ VT.fromList $ evalRandomData 
  (replicateM 10 (rtraverseIdentityTagged randHousehold)) 
  (mkStdGen 42)

randHousehold :: Rec (TaggedFunctor RandomData) Household
randHousehold = 
     tagFunctor [pr1|"household_name"|] houseStyle
  :& tagFunctor [pr1|"household_id"|]  (intBetween 5000 5010)
  :& RNil

details :: RelOp 
  '[ '("household_id", Int)
   , '("address", Text)
   ]
details = RelTable "details" implicitOrdList thing
  

toy :: RelOp 
  '[ '("toy_name", Int)
   , '("dog_id", Text)
   ]
toy = RelTable "toy" implicitOrdList thing

thing :: 
  ( rs ~ (a ': as)
  , ListAll rs (ConstrainSnd HasDefaultVector)
  , RecApplicative rs
  ) 
  => Relation rs
thing = RelationPresent $ rpureConstrained' 
  (TaggedFunctor (VectorVal G.empty)) 
  (reifyDictFun 
    (Proxy :: Proxy (ConstrainSnd HasDefaultVector)) 
    (rpure Proxy)
  )

dogs2 :: RelOp 
  '[ '("dog_weight", Int)
   , '("dog_size", Int)
   , '("dog_owner", Int)
   , '("dog_name", Text)
   , '("dog_id", Text)
   , '("dog_breed", Text)
   , '("dog_alive", Bool)
   , '("dog_age", Int)
   ]
dogs2 = RelTable "dogs2" implicitOrdList thing


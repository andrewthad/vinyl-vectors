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

main :: IO ()
main = do
  putStrLn $ showURelOp chosenOp
  putStrLn $ showURelOp $ canonizeURelOp chosenOp
  putStrLn $ showURelOp $ uPredGraphJoins $ canonizeURelOp chosenOp

chosenOp :: URelOp
chosenOp = myOp2

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

type Dog = 
  '[ '("person_id", Int)
   , '("dog_name", Text)
   , '("dog_age", Int)
   ]

myOp3 :: RelOp Dog
myOp3 = id
  $ restrict (valEq [pr1|"person_id"|] (3 :: Int))
  $ dogs

dogs :: RelOp Dog
dogs = RelTable "dogs" implicitOrdList thing
  -- where 
  -- r = RelationPresent 

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

people :: RelOp 
  '[ '("person_weight", Int)
   , '("person_name", Text)
   , '("person_id", Int)
   , '("household_id", Int)
   ]
people = RelTable "people" implicitOrdList thing

household :: RelOp 
  '[ '("household_name", Text)
   , '("household_id", Int)
   ]
household = RelTable "household" implicitOrdList thing

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
  (UncurriedTaggedFunctor (VectorVal G.empty)) 
  (reifyDictFun 
    (Proxy :: Proxy (ConstrainSnd HasDefaultVector)) 
    (rpure Proxy)
  )


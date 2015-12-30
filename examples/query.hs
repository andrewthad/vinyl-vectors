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
import Data.Vector.Vinyl.TypeLevel (ListAll)
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
  '[ 'NamedTypeOf "person_id" Int
   , 'NamedTypeOf "dog_name" Text
   , 'NamedTypeOf "dog_age" Int
   ]

myOp3 :: RelOp SymNamedTypeOfSymbol Dog
myOp3 = id
  $ restrict (valEq [pr1|"person_id"|] (3 :: Int))
  $ dogs

dogs :: RelOp SymNamedTypeOfSymbol Dog
dogs = RelTable "dogs" implicitOrdList r
  where 
  r = RelationPresent 

dogs2 :: RelOp SymNamedTypeOfSymbol
  '[ 'NamedTypeOf "dog_weight" Int
   , 'NamedTypeOf "dog_size" Int
   , 'NamedTypeOf "dog_owner" Int
   , 'NamedTypeOf "dog_name" Text
   , 'NamedTypeOf "dog_id" Text
   , 'NamedTypeOf "dog_breed" Text
   , 'NamedTypeOf "dog_alive" Bool
   , 'NamedTypeOf "dog_age" Int
   ]
dogs2 = RelTable "dogs2" implicitOrdList thing

people :: RelOp SymNamedTypeOfSymbol
  '[ 'NamedTypeOf "person_weight" Int
   , 'NamedTypeOf "person_name" Text
   , 'NamedTypeOf "person_id" Int
   , 'NamedTypeOf "household_id" Int
   ]
people = RelTable "people" implicitOrdList thing

household :: RelOp SymNamedTypeOfSymbol
  '[ 'NamedTypeOf "household_name" Text
   , 'NamedTypeOf "household_id" Int
   ]
household = RelTable "household" implicitOrdList thing

details :: RelOp SymNamedTypeOfSymbol
  '[ 'NamedTypeOf "household_id" Int
   , 'NamedTypeOf "address" Text
   ]
details = RelTable "details" implicitOrdList thing
  

toy :: RelOp SymNamedTypeOfSymbol
  '[ 'NamedTypeOf "toy_name" Int
   , 'NamedTypeOf "dog_id" Text
   ]
toy = RelTable "toy" implicitOrdList thing

thing :: (rs ~ (a ': as), ListAll rs (InnerHasDefaultVector SymNamedTypeOfSymbol), RecApplicative rs) 
  => Relation SymNamedTypeOfSymbol rs
thing = RelationPresent $ rpureConstrained' 
  (NamedWith (VectorVal G.empty)) 
  (reifyDictFun (Proxy :: Proxy (InnerHasDefaultVector SymNamedTypeOfSymbol)) (rpure Proxy))


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
  $ RelJoin toy
  $ RelJoin household
  $ equijoin [pr1|"person_id"|] [pr1|"dog_owner"|] people 
  $ project [pr|"dog_owner","dog_age"|] dogs2

dogs :: RelOp SymNamedTypeOfSymbol
  '[ 'NamedTypeOf "person_id" Int
   , 'NamedTypeOf "dog_name" Text
   , 'NamedTypeOf "dog_age" Int
   ]
dogs = RelTable "dogs" implicitOrdList thing

dogs2 :: RelOp SymNamedTypeOfSymbol
  '[ 'NamedTypeOf "dog_owner" Int
   , 'NamedTypeOf "dog_name" Text
   , 'NamedTypeOf "dog_id" Text
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

toy :: RelOp SymNamedTypeOfSymbol
  '[ 'NamedTypeOf "toy_name" Int
   , 'NamedTypeOf "dog_id" Text
   ]
toy = RelTable "toy" implicitOrdList thing

thing :: (ListAll rs (InnerHasDefaultVector SymNamedTypeOfSymbol), RecApplicative rs) 
  => Rec (NamedWith SymNamedTypeOfSymbol VectorVal) rs
thing = rpureConstrained' 
  (NamedWith (VectorVal G.empty)) 
  (reifyDictFun (Proxy :: Proxy (InnerHasDefaultVector SymNamedTypeOfSymbol)) (rpure Proxy))


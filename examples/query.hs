{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
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

main :: IO ()
main = do
  putStrLn $ showURelOp myOp
  putStrLn $ showURelOp $ canonizeURelOp myOp

myOp :: URelOp
myOp = toUnchecked 
  $ RelRestrict implicitSublist (PredEqValue 22 :: Pred SymNamedType '[ 'NamedType "person_id" Int])
  $ RelProject (implicitSublistSub 
      (Proxy :: Proxy '[ 'NamedType "person_name" Text, 'NamedType "person_id" Int])
    )
  $ RelRestrict implicitSublist (PredEqValue "Pranav" :: Pred SymNamedType '[ 'NamedType "person_name" Text])
  -- $ restrict (valEq (Proxy :: Proxy "dog_age") 44)
  $ RelRestrict implicitSublist (PredEqValue 44 :: Pred SymNamedType '[ 'NamedType "dog_age" Int])
  $ RelJoin dogs people

dogs :: RelOp SymNamedType 
  '[ 'NamedType "person_id" Int
   , 'NamedType "dog_name" Text
   , 'NamedType "dog_age" Int
   ]
dogs = RelTable "dogs" implicitOrdList thing

people :: RelOp SymNamedType 
  '[ 'NamedType "person_weight" Int
   , 'NamedType "person_name" Text
   , 'NamedType "person_id" Int
   ]
people = RelTable "people" implicitOrdList thing

thing :: (ListAll rs (InnerHasDefaultVector SymNamedType), RecApplicative rs) 
  => Rec (NamedWith SymNamedType VectorVal) rs
thing = rpureConstrained' 
    (NamedWith (VectorVal G.empty)) 
    (reifyDictFun (Proxy :: Proxy (InnerHasDefaultVector SymNamedType)) (rpure Proxy))

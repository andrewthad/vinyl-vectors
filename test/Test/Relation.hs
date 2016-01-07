module Test.Relation where

import Data.Relation
import Data.Vinyl hiding (Dict)
import Data.Vinyl.Lens (rcast)
import Data.Vinyl.Named
import Data.List.TypeLevel
import Data.Text (Text)
import Data.Vector.Vinyl.Default.Types (HasDefaultVector, VectorVal(..))
import Data.Proxy
import Data.Proxy.TH
import Data.Vinyl.Functor (Identity(..))
import Data.Tagged.Functor
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Vinyl.Default.NonEmpty.Tagged as VT
import Data.Time

type Person = Sort
  '[ '("person_name", Text)
   , '("person_id", Int)
   ]

type Employment = Sort
  '[ '("person_id", Int)
   , '("company_id", Int)
   , '("start_date", Day)
   ]

type Company = Sort
  '[ '("company_name", Text)
   , '("company_id", Int)
   ]

infix 9 ~>
(~>) :: proxy k -> v -> TaggedFunctor Identity '(k,v)
(~>) = tagIdentity

tag :: v -> TaggedFunctor Identity '(k,v)
tag = TaggedFunctor . Identity

-- note: Arnold has not worked anywhere
person :: RelOp Person
person = RelTable "person" implicitOrdList 
  $ RelationPresent $ VT.toRec $ VT.fromList
    [ ([pr1|"person_name"|] ~> "Drew") :& ([pr1|"person_id"|] ~> 1) :& RNil
    , ([pr1|"person_name"|] ~> "Alexa") :& ([pr1|"person_id"|] ~> 2) :& RNil
    , ([pr1|"person_name"|] ~> "Jordan") :& ([pr1|"person_id"|] ~> 3) :& RNil
    , ([pr1|"person_name"|] ~> "Mary") :& ([pr1|"person_id"|] ~> 4) :& RNil
    , ([pr1|"person_name"|] ~> "Arnold") :& ([pr1|"person_id"|] ~> 5) :& RNil
    , ([pr1|"person_name"|] ~> "Carlos") :& ([pr1|"person_id"|] ~> 6) :& RNil
    , ([pr1|"person_name"|] ~> "Juan") :& ([pr1|"person_id"|] ~> 7) :& RNil
    ]

-- note: no one has worked at company 1002
company :: RelOp Company
company = RelTable "company" implicitOrdList 
  $ RelationPresent $ VT.toRec $ VT.fromList
    [ ([pr1|"company_name"|] ~> "Dunder Mifflin") :& ([pr1|"company_id"|] ~> 1001) :& RNil
    , ([pr1|"company_name"|] ~> "Spade and Archer") :& ([pr1|"company_id"|] ~> 1002) :& RNil
    , ([pr1|"company_name"|] ~> "Monks Diner") :& ([pr1|"company_id"|] ~> 1003) :& RNil
    , ([pr1|"company_name"|] ~> "Moes Tavern") :& ([pr1|"company_id"|] ~> 1004) :& RNil
    , ([pr1|"company_name"|] ~> "The Krusty Krab") :& ([pr1|"company_id"|] ~> 1005) :& RNil
    ]

employment :: RelOp Employment
employment = RelTable "employment" implicitOrdList
  $ RelationPresent $ VT.toRec $ VT.fromList $ map rcast $ 
    ( [ tag 1 :& tag 1004 :& tag (fromGregorian 2002  8 13) :& RNil
      , tag 2 :& tag 1001 :& tag (fromGregorian 2004  3 23) :& RNil
      , tag 2 :& tag 1005 :& tag (fromGregorian 2001 10  2) :& RNil
      , tag 3 :& tag 1004 :& tag (fromGregorian 1998  3 19) :& RNil
      , tag 4 :& tag 1004 :& tag (fromGregorian 2001  3 12) :& RNil
      , tag 4 :& tag 1001 :& tag (fromGregorian 2008  4  9) :& RNil
      , tag 4 :& tag 1005 :& tag (fromGregorian 2012  3  8) :& RNil
      , tag 6 :& tag 1003 :& tag (fromGregorian 2002 11 14) :& RNil
      , tag 7 :& tag 1001 :& tag (fromGregorian 2001 11  7) :& RNil
      ] :: [ Rec (TaggedFunctor Identity) 
             '[ '("person_id", Int) , '("company_id", Int) , '("start_date", Day) ]
           ]
    )


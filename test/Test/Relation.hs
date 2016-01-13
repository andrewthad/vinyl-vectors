module Test.Relation where

import           Data.List.TypeLevel
import           Data.List.TypeLevel.Union      (Union)
import           Data.Proxy
import           Data.Proxy.TH
import           Data.Relation
import qualified Data.Relation.Backend          as Backend
import           Data.Tagged.Functor
import           Data.Text                      (Text)
import           Data.Time
import qualified Data.Vector.Generic            as G
import           Data.Vinyl                     hiding (Dict)
import           Data.Vinyl.DictFun
import           Data.Vinyl.Functor             (Lift (..))
import           Data.Vinyl.Functor             (Identity (..))
import           Data.Vinyl.Lens                (rcast)
import           Data.Vinyl.Named
import           Test.Framework.Providers.API   (Test)
import           Test.Framework.Providers.HUnit (testCase)
import           Test.HUnit                     (Assertion, (@?=))

data TestData a = TestData
  (forall rs. RelOp a rs -> IO (Backend.Test rs))
  (Rec (ListToRelation a) AllTemplates)

newtype ToRelation a rs = ToRelation
  (([Rec (TaggedFunctor Identity) rs] -> a rs) -> RelOp a rs)

newtype ListToRelation a rs = ListToRelation
  (Backend.Test rs -> a rs)

relationSpecTests :: forall a.
     (forall rs. RelOp a rs -> IO (Backend.Test rs))
  -> Rec (ListToRelation a) AllTemplates
  -> [Test]
relationSpecTests a b = map ($ TestData a b)
  [ testCase "Restriction Test 1 (Value Equality)" . testRestriction1
  , testCase "Restriction Test 2 (Disjunction)" . testRestriction2
  , testCase "Projection 1 (Contains Duplicates)" . testProjection1
  , testCase "Projection 2 (Empty Null)" . testProjection2
  , testCase "Projection 3 (Nonempty Null)" . testProjection3
  , testCase "Natural Join 1" . testNaturalJoin1
  , testCase "Natural Join 2" . testNaturalJoin2
  ]

type Person = Sort
  '[ '("person_name", Text)
   , '("person_id"  , Int)
   , '("person_age" , Int)
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

tag :: v -> TaggedFunctor Identity '(k,v)
tag = TaggedFunctor . Identity

-- note: Arnold has not worked anywhere
personTemplate :: Lift (->) (ListToRelation a) (RelOp a) Person
personTemplate = Lift $ \(ListToRelation f) -> RelTable
  (reifyDictFun (Proxy :: Proxy MinimalConstraints) (rpure Proxy))
  implicitOrdList
  $ f $ Backend.Test $ map rcast
    ( [ tag 1 :& tag "Drew"   :& tag 24 :& RNil
      , tag 2 :& tag "Alexa"  :& tag 14 :& RNil
      , tag 3 :& tag "Jordan" :& tag 39 :& RNil
      , tag 4 :& tag "Mary"   :& tag 66 :& RNil
      , tag 5 :& tag "Arnold" :& tag 14 :& RNil
      , tag 6 :& tag "Carlos" :& tag 20 :& RNil
      , tag 7 :& tag "Juan"   :& tag 52 :& RNil
      ] :: [ Rec (TaggedFunctor Identity)
             '[ '("person_id", Int) , '("person_name", Text) , '("person_age", Int) ]
           ]
    )

-- note: no one has worked at company 1002
companyTemplate :: Lift (->) (ListToRelation a) (RelOp a) Company
companyTemplate = Lift $ \(ListToRelation f) -> RelTable
  (reifyDictFun (Proxy :: Proxy MinimalConstraints) (rpure Proxy))
  implicitOrdList
  $ f $ Backend.Test
    [ tag "Dunder Mifflin"   :& tag 1001 :& RNil
    , tag "Spade and Archer" :& tag 1002 :& RNil
    , tag "Monks Diner"      :& tag 1003 :& RNil
    , tag "Moes Tavern"      :& tag 1004 :& RNil
    , tag "The Krusty Krab"  :& tag 1005 :& RNil
    ]

employmentTemplate :: Lift (->) (ListToRelation a) (RelOp a) Employment
employmentTemplate = Lift $ \(ListToRelation f) -> RelTable
  (reifyDictFun (Proxy :: Proxy MinimalConstraints) (rpure Proxy))
  implicitOrdList
  $ f $ Backend.Test $ map rcast $
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

allTemplates :: Rec (Lift (->) (ListToRelation a) (RelOp a)) '[Person,Company,Employment]
allTemplates = personTemplate :& companyTemplate :& employmentTemplate :& RNil

type AllTemplates = '[Person,Company,Employment]
type Fields (super :: [(k,*)]) (sub :: [k]) = [Rec (TaggedFunctor Identity) (SublistLookupManyUnordered super sub)]

testRestriction1 :: TestData a -> Assertion
testRestriction1 (TestData run f) = case rapply allTemplates f of
  person :& company :& employment :& RNil -> do
    actual <- run (restrict (valEq [pr1|"person_name"|] ("Carlos" :: Text)) person)
    actual @?= expected
  where
  expected = Backend.Test $ map rcast
    ( [tag 6 :& tag "Carlos" :& tag 20 :& RNil] ::
    Fields Person '["person_id","person_name","person_age"]
    )

testRestriction2 :: TestData a -> Assertion
testRestriction2 (TestData run f) = case rapply allTemplates f of
  person :& company :& employment :& RNil -> do
    actual <- run $ flip restrict person $
      predOr (valEq [pr1|"person_name"|] ("Carlos" :: Text))
             (valEq [pr1|"person_age"|] (14 :: Int))
    actual @?= expected
  where
  expected = Backend.Test $ map rcast
    ( [ tag 6 :& tag "Carlos" :& tag 20 :& RNil
      , tag 5 :& tag "Arnold" :& tag 14 :& RNil
      , tag 2 :& tag "Alexa"  :& tag 14 :& RNil
      ] ::
    Fields Person '["person_id","person_name","person_age"]
    )

testNaturalJoin1 :: TestData a -> Assertion
testNaturalJoin1 (TestData run f) = case rapply allTemplates f of
  person :& company :& employment :& RNil -> do
    actual <- run $ naturalJoin employment
                  $ flip restrict person $ predOr
                      (valEq [pr1|"person_id"|] (1 :: Int))
                      (valEq [pr1|"person_id"|] (2 :: Int))
    actual @?= expected
  where
  expected = Backend.Test $ map rcast
    ( [ tag 1 :& tag 1004 :& tag (fromGregorian 2002  8 13) :& tag "Drew"  :& tag 24 :& RNil
      , tag 2 :& tag 1001 :& tag (fromGregorian 2004  3 23) :& tag "Alexa" :& tag 14 :& RNil
      , tag 2 :& tag 1005 :& tag (fromGregorian 2001 10  2) :& tag "Alexa" :& tag 14 :& RNil
      ]
    :: Fields (Union Employment Person)
       '["person_id","company_id","start_date","person_name","person_age"]
    )

testNaturalJoin2 :: TestData a -> Assertion
testNaturalJoin2 (TestData run f) = case rapply allTemplates f of
  person :& company :& employment :& RNil -> do
    actual <- run $ restrict
                    ( predOr (valEq [pr1|"person_id"|] (1 :: Int))
                             (valEq [pr1|"person_id"|] (2 :: Int))
                    )
                  $ naturalJoin employment person
    actual @?= expected
  where
  expected = Backend.Test $ map rcast
    ( [ tag 1 :& tag 1004 :& tag (fromGregorian 2002  8 13) :& tag "Drew"  :& tag 24 :& RNil
      , tag 2 :& tag 1001 :& tag (fromGregorian 2004  3 23) :& tag "Alexa" :& tag 14 :& RNil
      , tag 2 :& tag 1005 :& tag (fromGregorian 2001 10  2) :& tag "Alexa" :& tag 14 :& RNil
      ]
    :: Fields (Union Employment Person)
       '["person_id","company_id","start_date","person_name","person_age"]
    )

testProjection1 :: TestData a -> Assertion
testProjection1 (TestData run f) = case rapply allTemplates f of
  person :& company :& employment :& RNil -> do
    actual <- run $ project [pr|"person_age"|] person
    actual @?= expected
  where
  expected = Backend.Test $ map rcast
    ( [ tag 24 :& RNil, tag 14 :& RNil, tag 39 :& RNil
      , tag 66 :& RNil, tag 20 :& RNil, tag 52 :& RNil
      ] ::
    Fields Person '["person_age"]
    )

testProjection2 :: TestData a -> Assertion
testProjection2 (TestData run f) = case rapply allTemplates f of
  person :& company :& employment :& RNil -> do
    actual <- run $ project (Proxy :: Proxy '[])
                  $ restrict (valEq [pr1|"person_age"|] (105 :: Int))
                  $ person
    actual @?= expected
  where
  expected = Backend.Test []

testProjection3 :: TestData a -> Assertion
testProjection3 (TestData run f) = case rapply allTemplates f of
  person :& company :& employment :& RNil -> do
    actual <- run $ project (Proxy :: Proxy '[])
                  $ restrict (valEq [pr1|"person_age"|] (14 :: Int))
                  $ person
    actual @?= expected
  where
  expected = Backend.Test [RNil]


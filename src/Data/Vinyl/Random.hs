{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor #-}

module Data.Vinyl.Random where

import Prelude hiding (const)
import System.Random (StdGen,RandomGen,randomR)
import Data.Text (Text)
import Data.List ((!!))
import Data.Vinyl.Core (Rec,rtraverse)
import Data.Vinyl.Functor (Identity(..))

newtype RandomData a = RandomData 
  { runRandomData :: StdGen -> (a, StdGen) }
  deriving (Functor)

evalRandomData :: RandomData a -> StdGen -> a
evalRandomData r g = fst (runRandomData r g)

instance Applicative RandomData where
  pure a = RandomData (\g -> (a,g))
  RandomData f1 <*> RandomData f2 = RandomData 
    (\g -> let (a,g') = f1 g
               (b,g'') = f2 g'
           in (a b, g'')
    )

instance Monad RandomData where
  return = pure
  RandomData f1 >>= h = RandomData $ \g ->
    let (a,g')        = f1 g
        RandomData f2 = h a
    in f2 g' 

randomElem :: RandomGen g => [a] -> g -> (a,g)
randomElem xs g = 
  let (i,g') = randomR (0, length xs - 1) g
  in (xs !! i, g')

const :: a -> RandomData a
const a = RandomData (\g -> (a,g))

intBetween :: Int -> Int -> RandomData Int
intBetween lo hi = RandomData (randomR (lo,hi))

company :: RandomData Text
company = RandomData $ randomElem
  [ "Acme, inc."
  , "Widget Corp"
  , "123 Warehousing"
  , "Demo Company"
  , "Smith and Co."
  , "Foo Bars"
  , "ABC Telecom"
  , "Fake Brothers"
  , "QWERTY Logistics"
  , "Demo, inc."
  , "Sample Company"
  , "Sample, inc"
  , "Acme Corp"
  , "Allied Biscuit"
  , "Ankh-Sto Associates"
  , "Extensive Enterprise"
  , "Galaxy Corp"
  , "Globo-Chem"
  , "Mr. Sparkle"
  , "Globex Corporation"
  , "LexCorp"
  , "LuthorCorp"
  , "North Central Positronics"
  , "Omni Consimer Products"
  , "Praxis Corporation"
  , "Sombra Corporation"
  , "Sto Plains Holdings"
  , "Tessier-Ashpool"
  , "Wayne Enterprises"
  , "Wentworth Industries"
  , "ZiffCorp"
  , "Bluth Company"
  , "Strickland Propane"
  , "Thatherton Fuels"
  , "Three Waters"
  , "Water and Power"
  , "Western Gas & Electric"
  , "Mammoth Pictures"
  , "Mooby Corp"
  , "Gringotts"
  , "Thrift Bank"
  , "Flowers By Irene"
  , "The Legitimate Businessmens Club"
  , "Osato Chemicals"
  , "Transworld Consortium"
  , "Universal Export"
  , "United Fried Chicken"
  , "Virtucon"
  , "Kumatsu Motors"
  , "Keedsler Motors"
  , "Powell Motors"
  , "Industrial Automation"
  , "Sirius Cybernetics Corporation"
  , "U.S. Robotics and Mechanical Men"
  , "Colonial Movers"
  , "Corellian Engineering Corporation"
  , "Incom Corporation"
  , "General Products"
  , "Leeding Engines Ltd."
  , "Blammo"
  , "Input, Inc."
  , "Mainway Toys"
  , "Videlectrix"
  , "Zevo Toys"
  , "Ajax"
  , "Axis Chemical Co."
  , "Barrytron"
  , "Carrys Candles"
  , "Cogswell Cogs"
  , "Spacely Sprockets"
  , "General Forge and Foundry"
  , "Duff Brewing Company"
  , "Dunder Mifflin"
  , "General Services Corporation"
  , "Monarch Playing Card Co."
  , "Krustyco"
  , "Initech"
  , "Roboto Industries"
  , "Primatech"
  , "Sonky Rubber Goods"
  , "St. Anky Beer"
  , "Stay Puft Corporation"
  , "Vandelay Industries"
  , "Wernham Hogg"
  , "Gadgetron"
  , "Burleigh and Stronginthearm"
  , "BLAND Corporation"
  , "Nordyne Defense Dynamics"
  , "Petrox Oil Company"
  , "Roxxon"
  , "McMahon and Tate"
  , "Sixty Second Avenue"
  , "Charles Townsend Agency"
  , "Spade and Archer"
  , "Megadodo Publications"
  , "Rouster and Sideways"
  , "C.H. Lavatory and Sons"
  , "Globo Gym American Corp"
  , "The New Firm"
  , "SpringShield"
  , "Compuglobalhypermeganet"
  , "Data Systems"
  , "Gizmonic Institute"
  , "Initrode"
  , "Taggart Transcontinental"
  , "Atlantic Northern"
  , "Niagular"
  , "Plow King"
  , "Big Kahuna Burger"
  , "Big T Burgers and Fries"
  , "Chez Quis"
  , "Chotchkies"
  , "The Frying Dutchman"
  , "Klimpys"
  , "The Krusty Krab"
  , "Monks Diner"
  , "Milliways"
  , "Minuteman Cafe"
  , "Taco Grande"
  , "Tip Top Cafe"
  , "Moes Tavern"
  , "Central Perk"
  , "Chasers"
  ]

houseStyle :: RandomData Text
houseStyle = RandomData $ randomElem
  [ "A-frame"
  , "Adirondack Architecture"
  , "American Craftsman"
  , "American Foursquare"
  , "Antebellum architecture"
  , "Arcachon villa"
  , "Art Deco"
  , "B-hut"
  , "Bay-and-gable"
  , "Bi-level"
  , "Broch"
  , "Bungalow"
  , "California bungalow"
  , "Cape Cod"
  , "Cape Dutch architecture"
  , "Catslide cottage"
  , "Chalet"
  , "Châteauesque"
  , "Colonial"
  , "Central-passage house"
  , "Colonial Revival"
  , "Conch house"
  , "Creole cottage"
  , "Dingbat"
  , "Dutch Colonial"
  , "Farmhouse"
  , "Federal"
  , "Federation"
  , "French Provincial"
  , "French Colonial"
  , "French-Canadian colonial"
  , "Georgian Colonial"
  , "Garrison"
  , "Georgian"
  , "Gothic revival"
  , "Greek Revival Style"
  , "Hall and parlor house"
  , "Hogan"
  , "Hut"
  , "Igloo"
  , "I-house"
  , "Indian veranda style"
  , "International Style"
  , "Italianate"
  , "Log house"
  , "Longhouse"
  , "Manor house"
  , "Mansion"
  , "Mar del Plata style"
  , "Mediterranean Revival Style"
  , "Mid-Century modern"
  , "Mobile home"
  , "Moderne"
  , "Neoclassical architecture"
  , "New Old House"
  , "Neo-eclectic"
  , "Octagon"
  , "Pacific lodge"
  , "Palladian"
  , "Populuxe"
  , "Portuguese Baroque"
  , "Post-modern"
  , "Prairie style"
  , "Pueblo style"
  , "Queen Anne"
  , "Queenslander"
  , "Rammed earth house"
  , "Ranch"
  , "Richardsonian Romanesque"
  , "Rumah Gadang"
  , "Rustic architecture"
  , "Saltbox"
  , "Second Empire"
  , "Sod dug-out"
  , "Sod house"
  , "Souterrain"
  , "Shingle style"
  , "Shotgun House"
  , "Southern plantation"
  , "Spanish colonial"
  , "Split-level garrison"
  , "Split level home"
  , "Stone Ender"
  , "Storybook house"
  , "Stick style"
  ]

americanMaleGivenName :: RandomData Text
americanMaleGivenName = RandomData $ randomElem
  [ "James" , "John" , "Robert" , "Michael" , "William"
  , "David" , "Richard" , "Charles" , "Joseph" , "Thomas"
  , "Christopher" , "Daniel" , "Paul" , "Mark" , "Donald"
  , "George" , "Kenneth" , "Steven" , "Edward" , "Brian"
  , "Ronald" , "Anthony" , "Kevin" , "Jason" , "Matthew"
  , "Gary" , "Timothy" , "Jose" , "Larry" , "Jeffrey"
  , "Frank" , "Scott" , "Eric" , "Stephen" , "Andrew"
  , "Raymond" , "Gregory" , "Joshua" , "Jerry" , "Dennis"
  , "Walter" , "Patrick" , "Peter" , "Harold" , "Douglas"
  , "Henry" , "Carl" , "Arthur" , "Ryan" , "Roger" , "Joe"
  , "Juan" , "Jack" , "Albert" , "Jonathan" , "Justin"
  , "Terry" , "Gerald" , "Keith" , "Samuel" , "Willie"
  , "Ralph" , "Lawrence" , "Nicholas" , "Roy" , "Benjamin"
  , "Bruce" , "Brandon" , "Adam" , "Harry" , "Fred" , "Wayne"
  , "Billy" , "Steve" , "Louis" , "Jeremy" , "Aaron"
  , "Randy" , "Howard" , "Eugene" , "Carlos" , "Russell"
  , "Bobby" , "Victor" , "Martin" , "Ernest" , "Phillip"
  , "Todd" , "Jesse" , "Craig" , "Alan" , "Shawn"
  , "Clarence" , "Sean" , "Philip" , "Chris" , "Johnny"
  , "Earl" , "Jimmy" , "Antonio"
  ]





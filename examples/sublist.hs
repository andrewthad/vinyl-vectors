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
{-# LANGUAGE PartialTypeSignatures #-}
import Data.List.TypeLevel
import Data.Vinyl.Named
import Data.Text (Text)
import Data.Proxy

main :: IO ()
main = do
  print (sublistSuperLength foo)
  print (sublistSubLength foo)
  print (sublistSuperLength bar)
  print (sublistSubLength bar)
  print (ordListLength thing)
  -- print (sublistSuperLength res)
  -- print (sublistSubLength res)

type Dog = 
  '[ '("dog_yaml", Bool)
   , '("dog_type", Text)
   , '("dog_size", Int)
   , '("dog_name", Text)
   , '("dog_id", Text)
   , '("dog_gyro", Text)
   , '("dog_falter", Text)
   , '("dog_carsickness", Text)
   , '("dog_breed", Text)
   , '("dog_alive", Bool)
   , '("dog_ailment", Text)
   , '("dog_age", Int)
   ]

type OtherDog = 
  '[ '("dog_size", Int)
   , '("dog_owner", Int)
   , '("dog_name", Text)
   , '("dog_id", Text)
   , '("dog_breed", Text)
   , '("dog_alive", Bool)
   , '("dog_age", Int)
   ]


thing :: OrdList Dog
thing = implicitOrdList

bar :: Sublist Dog
  '[ '("dog_breed", Text)
   , '("dog_ailment", Text)
   , '("dog_age", Int)
   ]
bar = implicitSublist

foo :: Sublist OtherDog
  '[ '("dog_owner", Int)
   , '("dog_breed", Text)
   , '("dog_age", Int)
   ]
foo = implicitSublist

test :: Sublist 
  '[ Int , Double , Bool , Double , Char , Integer , Char
   , Maybe Bool , Maybe Int , Char , Integer , Char , Maybe Bool 
   ]
  '[ Int , Double , Char , Char , Maybe Int , Maybe Bool ]
test = implicitSublist


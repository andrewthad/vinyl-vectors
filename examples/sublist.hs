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
  '[ 'NamedTypeOf "dog_yaml" Bool
   , 'NamedTypeOf "dog_type" Text
   , 'NamedTypeOf "dog_size" Int
   , 'NamedTypeOf "dog_name" Text
   , 'NamedTypeOf "dog_id" Text
   , 'NamedTypeOf "dog_gyro" Text
   , 'NamedTypeOf "dog_falter" Text
   , 'NamedTypeOf "dog_carsickness" Text
   , 'NamedTypeOf "dog_breed" Text
   , 'NamedTypeOf "dog_alive" Bool
   , 'NamedTypeOf "dog_ailment" Text
   , 'NamedTypeOf "dog_age" Int
   ]

type OtherDog = 
  '[ 'NamedTypeOf "dog_size" Int
   , 'NamedTypeOf "dog_owner" Int
   , 'NamedTypeOf "dog_name" Text
   , 'NamedTypeOf "dog_id" Text
   , 'NamedTypeOf "dog_breed" Text
   , 'NamedTypeOf "dog_alive" Bool
   , 'NamedTypeOf "dog_age" Int
   ]

-- bob :: Proxy (Union SymNamedTypeOfSymbol Dog OtherDog)
-- bob = Proxy

-- res :: _
-- res = unionSublist
--   (Proxy :: Proxy SymNamedTypeOfSymbol)
--   (implicitDictFun (Proxy :: Proxy IsNamedType) (sublistSuperToRec foo))
--   (implicitDictFun (Proxy :: Proxy IsNamedType) (sublistSuperToRec bar))
--   implicitOrdList
--   implicitOrdList
--   foo
--   bar

thing :: OrdList SymNamedTypeOfSymbol Dog
thing = implicitOrdList

bar :: Sublist Dog
  '[ 'NamedTypeOf "dog_breed" Text
   , 'NamedTypeOf "dog_ailment" Text
   , 'NamedTypeOf "dog_age" Int
   ]
bar = implicitSublist

foo :: Sublist OtherDog
  '[ 'NamedTypeOf "dog_owner" Int
   , 'NamedTypeOf "dog_breed" Text
   , 'NamedTypeOf "dog_age" Int
   ]
foo = implicitSublist

test :: Sublist 
  '[ Int , Double , Bool , Double , Char , Integer , Char
   , Maybe Bool , Maybe Int , Char , Integer , Char , Maybe Bool 
   ]
  '[ Int , Double , Char , Char , Maybe Int , Maybe Bool ]
test = implicitSublist


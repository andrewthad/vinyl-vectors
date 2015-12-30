{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
import Data.Proxy
import GHC.TypeLits

main :: IO ()
main = do
  putStrLn "Start"
  putStrLn "End"

type family IfOrd (a :: Ordering) (lt :: k) (eq :: k) (gt :: k) where 
  IfOrd LT lt eq gt = lt
  IfOrd EQ lt eq gt = eq
  IfOrd GT lt eq gt = gt

type family UnionCmp (o :: Ordering) (a :: Symbol) (as :: [Symbol]) (b :: Symbol) (bs :: [Symbol]) where
  UnionCmp LT a as b bs = b ': Union (a ': as) bs
  UnionCmp EQ a as b bs = a ': Union as bs
  UnionCmp GT a as b bs = a ': Union as (b ': bs)

type family Union (a :: [Symbol]) (b :: [Symbol]) :: [Symbol] where
  Union '[] '[] = '[]
  Union '[] (b ': bs) = b ': Union '[] bs 
  Union (a ': as) '[] = a ': Union as '[]
  Union (a ': as) (b ': bs) = UnionCmp (CmpSymbol a b) a as b bs

type A =
  '[ "zzz"
   , "foo"
   , "enough"
   , "dog"
   , "daisy"
   , "bob"
   , "baz"
   , "bar"
   ]

type B =
  '[ "zzz"
   , "type"
   , "super"
   , "silent"
   , "gorge"
   , "foo"
   , "bob"
   , "baz"
   , "bar"
   , "bam"
   , "aleph"
   , "agarsh"
   ]

foo :: Proxy (Union A B)
foo = Proxy



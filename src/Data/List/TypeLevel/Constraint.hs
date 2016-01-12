{-# LANGUAGE FlexibleInstances #-}
module Data.List.TypeLevel.Constraint where

import           GHC.Exts (Constraint)

-- | A constraint on each element of a type-level list.
type family ListAll (ts :: [k]) (c :: k -> Constraint) :: Constraint where
  ListAll '[] c = ()
  ListAll (t ': ts) c = (c t, ListAll ts c)

class (ca x, cb x) => (ca :&: cb) x
instance (ca x, cb x) => (ca :&: cb) x

type family RequireEquality (a :: k) (b :: k) (c :: j) :: j where
  RequireEquality a a c = c


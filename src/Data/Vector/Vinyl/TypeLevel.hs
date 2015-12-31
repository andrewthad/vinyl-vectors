{-# LANGUAGE DataKinds      #-}
{-# LANGUAGE GADTs          #-}
{-# LANGUAGE TypeOperators  #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds      #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE FlexibleInstances   #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  Andrew Martin
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Andrew Martin <andrew.thaddeus@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Try to merge some of this into vinyl at some point.
-----------------------------------------------------------------------------
module Data.Vector.Vinyl.TypeLevel
  ( ListAll
  , Fst
  , Snd
  , ConstrainFst
  , ConstrainSnd
  ) where

import GHC.Exts (Constraint)

-- | A constraint on each element of a type-level list.
type family ListAll (ts :: [k]) (c :: k -> Constraint) :: Constraint where
  ListAll '[] c = ()
  ListAll (t ': ts) c = (c t, ListAll ts c)

-- | First element of a type pair.
type family Fst k where
    Fst '(a,b) = a

-- |Second element of a type pair.
type family Snd k where
    Snd '(a,b) = b

class c (Fst x) => ConstrainFst (c :: j -> Constraint) (x :: (j,k))
instance c (Fst x) => ConstrainFst c x

class c (Snd x) => ConstrainSnd (c :: k -> Constraint) (x :: (j,k))
instance c (Snd x) => ConstrainSnd c x

-- For some reason, these two type families don't work. They wont
-- reduce properly when we learn that ( r ~ r1 ': rs)
--
-- type family ListAllFst (rs :: [(a,b)]) (c :: b -> Constraint) :: Constraint where
--   ListAllFst '[] c = ()
--   ListAllFst ( r ': rs) c = (c (Fst r), ListAllFst rs c)
-- 
-- type family ListAllSnd (rs :: [(a,b)]) (c :: b -> Constraint) :: Constraint where
--   ListAllSnd '[] c = ()
--   ListAllSnd ( r ': rs) c = (c (Snd r), ListAllSnd rs c)


{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  Andrew Martin
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Andrew Martin <andrew.thaddeus@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- Try to merge this into vinyl at some point.
-----------------------------------------------------------------------------
module Data.Vector.Vinyl.TypeLevel
  ( ListAll
  ) where

import GHC.Exts (Constraint)

-- | A constraint on each element of a type-level list.
type family ListAll (ts :: [k]) (c :: k -> Constraint) :: Constraint where
  ListAll '[] c = ()
  ListAll (t ': ts) c = (c t, ListAll ts c)

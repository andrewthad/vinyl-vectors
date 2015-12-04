{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Vector.Vinyl.TypeLevel
  ( ListAll
  ) where

import GHC.Exts (Constraint)

-- | A constraint on each element of a type-level list.
type family ListAll (ts :: [k]) (c :: k -> Constraint) :: Constraint where
  ListAll '[] c = ()
  ListAll (t ': ts) c = (c t, ListAll ts c)

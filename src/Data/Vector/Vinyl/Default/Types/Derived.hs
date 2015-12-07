{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
module Data.Vector.Vinyl.Default.Types.Derived where

import Data.Default
import Data.Vector.Vinyl.Default.Types.Deriving (derivingVector)
import Data.Vector.Unboxed.Base (Unbox)

derivingUnbox "Maybe" ''Unbox
  [t| forall a. (Default a, Unbox a) => Maybe a -> (Bool, a) |]
  [| maybe (False, def) (\ x -> (True, x)) |]
  [| \ (b, x) -> if b then Just x else Nothing |]



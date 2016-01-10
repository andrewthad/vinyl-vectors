{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}

-----------------------------------------------------------------------------
-- |
-- Copyright   :  Andrew Martin
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Andrew Martin <andrew.thaddeus@gmail.com>
-- Stability   :  experimental
-- Portability :  non-portable
--
-- This module uses the "constraints" package to prove that if all of the
-- columns satisfy the 'HasDefaultVector' constraint, then a vector
-- parameterized over the record has an instance of the generic vector
-- typeclass.
-----------------------------------------------------------------------------
module Data.Vector.Vinyl.Default.Empty.Monomorphic.Implication where

import           Data.Constraint
import           Data.List.TypeLevel.Constraint                       (ListAll)
import           Data.Vector.Vinyl.Default.Empty.Monomorphic.Internal
import           Data.Vector.Vinyl.Default.Types                      (HasDefaultVector)
import           Data.Vinyl.Core                                      (Rec (..))
import           Data.Vinyl.Functor                                   (Identity (..))

import qualified Data.Vector.Generic                                  as G
import qualified Data.Vector.Generic.Mutable                          as GM

listAllVector :: Rec proxy rs
              -> ListAll rs HasDefaultVector :- G.Vector Vector (Rec Identity rs)
listAllVector RNil = Sub Dict
listAllVector (_ :& rs) = Sub $ case listAllVector rs of
  Sub Dict -> Dict

listAllMVector :: Rec proxy rs
              -> ListAll rs HasDefaultVector :- GM.MVector MVector (Rec Identity rs)
listAllMVector RNil = Sub Dict
listAllMVector (_ :& rs) = Sub $ case listAllMVector rs of
  Sub Dict -> Dict

-- listAllVectorBoth :: Rec proxy rs
--   -> ListAll rs HasDefaultVector :- (GM.MVector MVector (Rec Identity rs), G.Vector Vector (Rec Identity rs))
-- listAllVectorBoth RNil = Sub Dict
-- listAllVectorBoth (_ :& rs) = Sub $ case listAllVectorBoth rs of
--   Sub Dict -> Dict


{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

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
module Data.Vector.Vinyl.Default.NonEmpty.Polymorphic.Implication where

import Data.Constraint
import Data.Vector.Vinyl.Default.NonEmpty.Polymorphic.Internal
import Data.Vinyl.Core (Rec(..))
import Data.Vinyl.Functor (Identity(..))
import Data.Vinyl.TypeLevel (RecAll)

import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Generic as G

listAllVector :: (rs ~ (a ': as))
              => Rec f rs 
              -> RecAll f rs HasDefaultVector :- G.Vector Vector (Rec f rs)
listAllVector (_ :& RNil) = Sub Dict
listAllVector (_ :& rs@(_ :& _)) = Sub $ case listAllVector rs of
  Sub Dict -> Dict

listAllMVector :: (rs ~ (a ': as))
               => Rec f rs 
               -> RecAll f rs HasDefaultVector :- GM.MVector MVector (Rec f rs)
listAllMVector (_ :& RNil) = Sub Dict
listAllMVector (_ :& rs@(_ :& _)) = Sub $ case listAllMVector rs of
  Sub Dict -> Dict

listAllMVector' :: (rs ~ (a ': as))
                => proxy1 f
                -> Rec proxy2 rs 
                -> RecAll f rs HasDefaultVector :- GM.MVector MVector (Rec f rs)
listAllMVector' _ (_ :& RNil) = Sub Dict
listAllMVector' p (_ :& rs@(_ :& _)) = Sub $ case listAllMVector' p rs of
  Sub Dict -> Dict



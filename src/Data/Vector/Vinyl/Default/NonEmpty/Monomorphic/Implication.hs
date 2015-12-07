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
module Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Implication where

import Data.Constraint
import Data.Vector.Vinyl.Default.NonEmpty.Monomorphic.Internal
import Data.Vinyl.Core (Rec(..))
import Data.Vinyl.Functor (Identity(..))
import Data.Vector.Vinyl.TypeLevel (ListAll)

import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Generic as G

listAllVector :: (rs ~ (a ': as))
              => Rec proxy rs 
              -> ListAll rs HasDefaultVector :- G.Vector Vector (Rec Identity rs)
listAllVector (_ :& RNil) = Sub Dict
listAllVector (_ :& rs@(_ :& _)) = Sub $ case listAllVector rs of
  Sub Dict -> Dict

listAllMVector :: (rs ~ (a ': as))
              => Rec proxy rs 
              -> ListAll rs HasDefaultVector :- GM.MVector MVector (Rec Identity rs)
listAllMVector (_ :& RNil) = Sub Dict
listAllMVector (_ :& rs@(_ :& _)) = Sub $ case listAllMVector rs of
  Sub Dict -> Dict

-- listAllVectorBoth :: Rec proxy rs 
--   -> ListAll rs HasDefaultVector :- (GM.MVector MVector (Rec Identity rs), G.Vector Vector (Rec Identity rs))
-- listAllVectorBoth RNil = Sub Dict
-- listAllVectorBoth (_ :& rs) = Sub $ case listAllVectorBoth rs of
--   Sub Dict -> Dict

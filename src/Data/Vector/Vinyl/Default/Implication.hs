{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

module Data.Vector.Vinyl.Default.Implication where

import Data.Constraint
import Data.Vector.Vinyl.Default.Internal
import Data.Vinyl.Core (Rec(..))
import Data.Vinyl.Functor (Identity(..))
import Data.Vector.Vinyl.TypeLevel (ListAll)

import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Generic as G

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


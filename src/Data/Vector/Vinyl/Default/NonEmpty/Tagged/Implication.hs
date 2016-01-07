{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module Data.Vector.Vinyl.Default.NonEmpty.Tagged.Implication where

import Data.Constraint
import Data.Vector.Vinyl.Default.NonEmpty.Tagged.Internal
import Data.Vinyl.Core (Rec(..))
import Data.Vinyl.Functor (Identity(..))
import Data.List.TypeLevel (ListAll,ConstrainSnd)
import Data.Vector.Vinyl.Default.Types (HasDefaultVector)

import qualified Data.Vector.Generic.Mutable as GM
import qualified Data.Vector.Generic as G
import Data.Proxy
import Data.Tagged.Functor

listAllVector :: (rs ~ (a ': as))
              => Rec proxy rs 
              -> ListAll rs (ConstrainSnd HasDefaultVector) :- G.Vector (Vector 'KProxy) (Rec (TaggedFunctor Identity) rs)
listAllVector (_ :& RNil) = Sub Dict
listAllVector (_ :& rs@(_ :& _)) = Sub $ case listAllVector rs of
  Sub Dict -> Dict

listAllMVector :: (rs ~ (a ': as))
              => Rec proxy rs 
              -> ListAll rs (ConstrainSnd HasDefaultVector) :- GM.MVector (MVector 'KProxy) (Rec (TaggedFunctor Identity) rs)
listAllMVector (_ :& RNil) = Sub Dict
listAllMVector (_ :& rs@(_ :& _)) = Sub $ case listAllMVector rs of
  Sub Dict -> Dict


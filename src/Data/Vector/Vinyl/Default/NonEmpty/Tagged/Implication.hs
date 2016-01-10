{-# LANGUAGE DataKinds     #-}
{-# LANGUAGE GADTs         #-}
{-# LANGUAGE TypeOperators #-}

module Data.Vector.Vinyl.Default.NonEmpty.Tagged.Implication where

import           Data.Constraint
import           Data.List.TypeLevel.Constraint                     (ListAll)
import           Data.Tuple.TypeLevel                               (ConstrainSnd)
import           Data.Vector.Vinyl.Default.NonEmpty.Tagged.Internal
import           Data.Vector.Vinyl.Default.Types                    (HasDefaultVector)
import           Data.Vinyl.Core                                    (Rec (..))
import           Data.Vinyl.Functor                                 (Identity (..))

import           Data.Proxy
import           Data.Tagged.Functor
import qualified Data.Vector.Generic                                as G
import qualified Data.Vector.Generic.Mutable                        as GM

listAllVector :: forall (rs :: [(k,*)]) a as proxy.
     (rs ~ (a ': as))
     => Rec proxy rs
     -> ListAll rs (ConstrainSnd HasDefaultVector)
        :- G.Vector (Vector ('KProxy :: KProxy k)) (Rec (TaggedFunctor Identity) rs)
listAllVector (_ :& RNil) = Sub Dict
listAllVector (_ :& rs@(_ :& _)) = Sub $ case listAllVector rs of
  Sub Dict -> Dict

listAllMVector :: forall (rs :: [(k,*)]) a as proxy.
     (rs ~ (a ': as))
  => Rec proxy rs
  -> ListAll rs (ConstrainSnd HasDefaultVector)
     :- GM.MVector (MVector ('KProxy :: KProxy k)) (Rec (TaggedFunctor Identity) rs)
listAllMVector (_ :& RNil) = Sub Dict
listAllMVector (_ :& rs@(_ :& _)) = Sub $ case listAllMVector rs of
  Sub Dict -> Dict


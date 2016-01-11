{-# LANGUAGE PolyKinds #-}

module Data.Vinyl.Class.Implication where

import           Data.Constraint
import           Data.List.TypeLevel.Cmp        (eqTProxy)
import           Data.List.TypeLevel.Constraint (ListAll)
import           Data.Proxy                     (Proxy (Proxy))
import           Data.Tagged.Functor            (TaggedFunctor (..))
import           Data.Tuple.TypeLevel           (ConstrainSnd, Snd)
import           Data.Type.Equality             ((:~:) (Refl))
import           Data.Typeable
import           Data.Vinyl.Core                (Rec (..))
import           Data.Vinyl.TypeLevel           (RecAll)

recAllEq' :: Rec f rs -> (RecAll f rs Eq :- Eq (Rec f rs))
recAllEq' RNil = Sub Dict
recAllEq' (_ :& rs) = Sub $ case recAllEq' rs of
  Sub Dict -> Dict

recAllEq :: Proxy f -> Rec proxy rs -> (RecAll f rs Eq :- Eq (Rec f rs))
recAllEq _ RNil = Sub Dict
recAllEq p (_ :& rs) = Sub $ case recAllEq p rs of
  Sub Dict -> Dict

recAllOrd' :: Rec f rs -> (RecAll f rs Ord :- Ord (Rec f rs))
recAllOrd' RNil = Sub Dict
recAllOrd' (_ :& rs) = Sub $ case recAllOrd' rs of
  Sub Dict -> Dict

recAllOrd :: Proxy f -> Rec proxy rs -> (RecAll f rs Ord :- Ord (Rec f rs))
recAllOrd _ RNil = Sub Dict
recAllOrd p (_ :& rs) = Sub $ case recAllOrd p rs of
  Sub Dict -> Dict

listAllOrd :: forall f rs proxy.
  Proxy f -> Rec proxy rs -> (forall a. Ord a :- Ord (f a)) -> (ListAll rs Ord :- Ord (Rec f rs))
listAllOrd f pRec cEntail =
  Sub $ case listAllToRecAll (Proxy :: Proxy Ord) f pRec cEntail of
    Sub Dict -> case recAllOrd f pRec of
      Sub Dict -> Dict

listAllToRecAll :: forall c f rs proxy.
  Proxy c -> Proxy f -> Rec proxy rs -> (forall a. c a :- c (f a)) -> (ListAll rs c :- RecAll f rs c)
listAllToRecAll _ _ RNil _ = Sub Dict
listAllToRecAll c f ((_ :: proxy r) :& rs) cEntail =
  Sub $ case listAllToRecAll c f rs cEntail of
    Sub Dict -> case (cEntail :: (c r :- c (f r))) of
      Sub Dict -> Dict

listAllToTaggedRecAll :: forall (c :: * -> Constraint) f (rs :: [(k,*)]) proxy.
  Proxy c -> Proxy f -> Rec proxy rs
  -> (forall (a :: (k,*)). c (Snd a) :- c (TaggedFunctor f a))
  -> (ListAll rs (ConstrainSnd c) :- RecAll (TaggedFunctor f) rs c)
listAllToTaggedRecAll _ _ RNil _ = Sub Dict
listAllToTaggedRecAll c f ((_ :: proxy r) :& rs) cEntail =
  Sub $ case listAllToTaggedRecAll c f rs cEntail of
    Sub Dict -> case (cEntail :: (c (Snd r) :- c (TaggedFunctor f r))) of
      Sub Dict -> Dict

eqTRec :: (ListAll rs Typeable, ListAll ss Typeable)
  => Rec proxy rs -> Rec proxy ss -> Maybe (rs :~: ss)
eqTRec RNil RNil = Just Refl
eqTRec (r :& rs) (s :& ss) = case eqTProxy r s of
  Nothing -> Nothing
  Just Refl -> case eqTRec rs ss of
    Nothing -> Nothing
    Just Refl -> Just Refl

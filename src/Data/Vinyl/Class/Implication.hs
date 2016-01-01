module Data.Vinyl.Class.Implication where

import Data.Vinyl.Core (Rec(..))
import Data.Vinyl.TypeLevel (RecAll)
import Data.Constraint
import Data.Proxy (Proxy(Proxy))
import Data.List.TypeLevel (ListAll)

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


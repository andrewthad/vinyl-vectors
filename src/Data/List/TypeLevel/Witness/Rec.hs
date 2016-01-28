module Data.List.TypeLevel.Witness.Rec where

import           Data.List.TypeLevel.Witness
import           Data.Tagged.Functor
import           Data.Vinyl.Core             hiding (Dict)
import           Data.Vinyl.Functor          (Identity (..))

rename :: RemoveElem '(k1,v) rs ss -> RemoveElem '(k2,v) ts ss
       -> Rec (TaggedFunctor Identity) rs -> Rec (TaggedFunctor Identity) ts
rename rm ins rec = case remove rm rec of
  (TaggedFunctor val, recMinus) -> insert ins (TaggedFunctor val) recMinus

remove :: RemoveElem r rs ss -> Rec f rs -> (f r, Rec f ss)
remove = go
  where
  go :: forall f r rs ss. RemoveElem r rs ss -> Rec f rs -> (f r, Rec f ss)
  go RemoveElemDone (r :& rs) = (r, rs)
  go (RemoveElemNext rmNext) (r :& rs) = let (val, rec) = go rmNext rs in (val, r :& rec)

insert :: RemoveElem r rs ss -> f r -> Rec f ss -> Rec f rs
insert = go
  where
  go :: forall f r rs ss. RemoveElem r rs ss -> f r -> Rec f ss -> Rec f rs
  go RemoveElemDone v rs = v :& rs
  go (RemoveElemNext rmNext) v (r :& rs) = r :& go rmNext v rs


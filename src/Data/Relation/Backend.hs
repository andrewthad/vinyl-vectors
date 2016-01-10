{-# LANGUAGE PolyKinds #-}
module Data.Relation.Backend where

import qualified Data.List                       as List
import           Data.List.TypeLevel
import           Data.List.TypeLevel.Constraint  ((:&:))
import           Data.Set                        (Set)
import           Data.Tagged.Functor             (TaggedFunctor)
import           Data.Tuple.TypeLevel
import           Data.Vector.Vinyl.Default.Types (HasDefaultVector, VectorVal)
import           Data.Vinyl.Core                 hiding (Dict)
import           Data.Vinyl.DictFun
import           Data.Vinyl.Functor              (Compose, Identity)

newtype Naive rs = Naive {getNaive :: (Set (Rec (TaggedFunctor Identity) rs)) }
newtype Test rs = Test { getTest :: [Rec (TaggedFunctor Identity) rs] }

instance (Ord (Rec (TaggedFunctor Identity) rs)) => Eq (Test rs) where
  Test a == Test b = List.sort a == List.sort b

instance (Show (Rec (TaggedFunctor Identity) rs)) => Show (Test rs) where
  show (Test a) = "Test (" ++ show a ++ ")"

data BasicInner rs = BasicInner
  (Rec (DictFun (ConstrainSnd HasDefaultVector :&: ConstrainSnd Show)) rs)
  (Rec (TaggedFunctor VectorVal) rs)

data Basic rs = Basic !String !(Common BasicInner rs)

data NullRelArity = NullRelOne | NullRelZero
  deriving (Show,Eq)

data Common (a :: [(k,*)] -> *) (rs :: [(k,*)]) where
  CommonNull    :: NullRelArity -> Common a '[]
  CommonPresent :: a (r ': rs) -> Common a (r ': rs)

nullRelArityToInt :: NullRelArity -> Int
nullRelArityToInt a = case a of
  NullRelOne  -> 1
  NullRelZero -> 0


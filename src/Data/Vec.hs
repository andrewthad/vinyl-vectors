module Data.Vec where

import Data.List.TypeLevel (Nat(..),Natty(..),HasNatty(..))
import Data.Traversable (fmapDefault,foldMapDefault)
import Data.List.NonEmpty (NonEmpty((:|)))

data Vec (n :: Nat) a where
  VecNil  :: Vec 'Zero a
  VecCons :: !a -> Vec n a -> Vec ('Succ n) a

instance Show a => Show (Vec n a) where
  show VecNil = "VecNil"
  show (VecCons a v) = "VecCons (" ++ show a ++ " " ++ show v ++ ")"

instance Functor (Vec n) where
  fmap = fmapDefault

instance Foldable (Vec n) where
  foldMap = foldMapDefault

instance Traversable (Vec n) where
  traverse _ VecNil = pure VecNil
  traverse f (VecCons v vs) = VecCons <$> f v <*> traverse f vs

instance HasNatty n => Applicative (Vec n) where
  pure = vcopies natty
  (<*>) = vapp

vcopies :: Natty n -> x -> Vec n x
vcopies Zeroy _ = VecNil
vcopies (Succy n) x = VecCons x (vcopies n x)

vapp :: Vec n (s -> t) -> Vec n s -> Vec n t
vapp VecNil VecNil = VecNil
vapp (VecCons f fs) (VecCons s ss) = VecCons (f s) (vapp fs ss)

data SomeVec a where
  SomeVec :: forall (n :: Nat) a. HasNatty n => Vec n a -> SomeVec a

data SomeNonEmptyVec a where
  SomeNonEmptyVec :: forall (n :: Nat) a. HasNatty n => Vec ('Succ n) a -> SomeNonEmptyVec a

listToVec :: [a] -> SomeVec a
listToVec [] = SomeVec VecNil
listToVec (a : as) = case listToVec as of
  SomeVec vs -> SomeVec (VecCons a vs)

nonEmptyToVec :: NonEmpty a -> SomeNonEmptyVec a
nonEmptyToVec (a :| as) = case listToVec as of
  SomeVec vs -> SomeNonEmptyVec (VecCons a vs)

vecToList :: Vec n a -> [a]
vecToList VecNil = []
vecToList (VecCons a as) = a : vecToList as

vecToNonEmpty :: Vec ('Succ n) a -> NonEmpty a
vecToNonEmpty (VecCons a as) = a :| vecToList as


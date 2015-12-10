{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE FlexibleInstances #-}
module Data.Vinyl.Arbitrary where

import Test.QuickCheck.Arbitrary
import Data.Vinyl.Core (Rec(..))

newtype ArbitraryRec f rs = ArbitraryRec { getArbitraryRec :: Rec f rs }
  deriving (Show, Eq)

instance Arbitrary (ArbitraryRec f '[]) where
  arbitrary = pure (ArbitraryRec RNil)
  shrink (ArbitraryRec RNil) = []

instance (Arbitrary (f a), Arbitrary (ArbitraryRec f as)) => Arbitrary (ArbitraryRec f (a ': as)) where
  arbitrary = fmap ArbitraryRec ((:&) <$> arbitrary <*> fmap getArbitraryRec arbitrary)
  shrink (ArbitraryRec (r :& rs)) = fmap ArbitraryRec $ (:&)
    <$> shrink r
    <*> fmap getArbitraryRec (shrink (ArbitraryRec rs))

{-# LANGUAGE FlexibleInstances #-}
module Data.TypeString where

import           Data.Proxy
import           GHC.TypeLits

class TypeString t where
  typeString :: proxy t -> String
instance KnownSymbol t => TypeString (t :: Symbol) where
  typeString _ = symbolVal (Proxy :: Proxy t)
instance (KnownSymbol t,KnownSymbol s) => TypeString ( '(t,s) :: (Symbol,Symbol)) where
  typeString _ = symbolVal (Proxy :: Proxy t) ++ "." ++ symbolVal (Proxy :: Proxy s)


{-# LANGUAGE ConstraintKinds, FlexibleContexts, GADTs, TemplateHaskell, TypeOperators #-}
{-# LANGUAGE DataKinds #-}
module Data.Proxy.TH 
  ( pr
  , pr1
  ) where

import Language.Haskell.TH
import Language.Haskell.TH.Quote
import Data.Proxy
import Data.Char (isUpper, isSpace)
import Data.List

-- I took this from Anthony Cowley's Frames library.

-- * Proxy Syntax

-- | A proxy value quasiquoter; a way of passing types as
-- values. It always makes a list of values.
-- @[pr|A,B,C|]@ will splice in a value of @Proxy :: Proxy
-- [A,B,C]@. If we have a record type with @Name@ and @Age@ among
-- other fields, we can write @select @[pr|Name,Age|]@ for a function
-- that extracts those fields from a larger record.
pr :: QuasiQuoter
pr = QuasiQuoter mkProxy undefined undefined undefined
  where mkProxy s = let ts = map strip $ splitOn ',' s
                        cons = mapM (conT . mkName) ts
                        strLits = fmap mkList ((fmap.fmap) LitT (mapM (strTyLit . init . tail) ts))
                        mkList = foldr (AppT . AppT PromotedConsT) PromotedNilT
                    in case ts of
                         (h@(t:_) : _)
                             | isUpper t -> [|Proxy::Proxy $(fmap mkList cons)|]
                             | t == '"'  -> [|Proxy::Proxy $(strLits)|]
                             | otherwise -> error "incorrect use of pr quasiquoter"
                         [] -> error "pr: empty list" 

pr1 :: QuasiQuoter
pr1 = QuasiQuoter mkProxy undefined undefined undefined
  where mkProxy s = let sing x = id -- AppT (AppT PromotedConsT x) PromotedNilT
                        strLit = fmap LitT (strTyLit . init . tail $ s)
                    in case s of
                         t:_
                           | isUpper t ->
                             [|Proxy::Proxy $((conT (mkName s)))|]
                           | t == '"'  -> 
                             [|Proxy::Proxy $(strLit)|]
                           | otherwise ->
                             [|Proxy::Proxy $((varT $ mkName s))|]
                         _ -> error "Empty string passed to pr1"

-- | Split on a delimiter.
splitOn :: Eq a => a -> [a] -> [[a]]
splitOn d = go
  where go [] = []
        go xs = let (h,t) = break (== d) xs
                in case t of
                     [] -> [h]
                     (_:t') -> h : go t'

-- | Remove white space from both ends of a 'String'.
strip :: String -> String
strip = takeWhile (not . isSpace) . dropWhile isSpace

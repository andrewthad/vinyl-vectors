{-# LANGUAGE CPP #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS -Wall #-}

{-|
Module:      Data.Vector.Unboxed.Deriving
Copyright:   © 2012−2015 Liyang HU
License:     BSD3
Maintainer:  vector-th-unbox@liyang.hu
Stability:   experimental
Portability: non-portable
-}

module Data.Vector.Vinyl.Default.Types.Deriving
    ( -- $usage
      derivingVector
    ) where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative
#endif
import Control.Arrow
import Control.Monad
import Data.Char (isAlphaNum)
import qualified Data.Vector.Generic as G
import qualified Data.Vector.Generic.Mutable as M
-- import Data.Vector.Unboxed.Base (MVector (..), Vector (..), Unbox)
import Language.Haskell.TH

-- Create a @Pat@ bound to the given name and an @Exp@ for said binding.
newPatExp :: String -> Q (Pat, Exp)
newPatExp = fmap (VarP &&& VarE) . newName

data Common = Common
    { mvName, vName :: Name
    , i, n, mv, mv', v :: (Pat, Exp) }

common :: String -> Q Common
common name = do
    -- A bit looser than “Haskell 2010: §2.4 Identifiers and Operators”…
    let valid c = c == '_' || c == '\'' || c == '#' || isAlphaNum c
    unless (all valid name) $ do
        fail (show name ++ " is not a valid constructor suffix!")
    let mvName = mkName ("MV_" ++ name)
    let vName = mkName ("V_" ++ name)
    i <- newPatExp "idx"
    n <- newPatExp "len"
    mv  <- first (ConP mvName . (:[])) <$> newPatExp "mvec"
    mv' <- first (ConP mvName . (:[])) <$> newPatExp "mvec'"
    v   <- first (ConP vName  . (:[])) <$> newPatExp "vec"
    return Common {..}

-- Turn any 'Name' into a capturable one.
capture :: Name -> Name
#if __GLASGOW_HASKELL__ == 704
capture = mkName . nameBase
#else
capture = id
#endif

liftE :: Exp -> Exp -> Exp
liftE e = InfixE (Just e) (VarE 'liftM) . Just

-- Create a wrapper for the given function with the same 'nameBase', given
-- a list of argument bindings and expressions in terms of said bindings.
-- A final coercion (@Exp → Exp@) is applied to the body of the function.
-- Complimentary @INLINE@ pragma included.
wrap :: Name -> [(Pat, Exp)] -> (Exp -> Exp) -> [Dec]
wrap fun (unzip -> (pats, exps)) coerce = [inline, method] where
    name = capture fun
    inline = PragmaD (InlineP name Inline FunLike AllPhases)
    body = coerce $ foldl AppE (VarE fun) exps
    method = FunD name [Clause pats (NormalB body) []]

{-| Let's consider a more complex example: suppose we want an @Unbox@
instance for @Maybe a@. We could encode this using the pair @(Bool, a)@,
with the boolean indicating whether we have @Nothing@ or @Just@ something.
This encoding requires a dummy value in the @Nothing@ case, necessitating an
additional <http://hackage.haskell.org/package/data-default/docs/Data-Default.html#t:Default Default>
constraint. Thus:

>derivingVector "Maybe"
>    [t| ∀ a. (Default a, Unbox a) ⇒ Maybe a → (Bool, a) |]
>    [| maybe (False, def) (\ x → (True, x)) |]
>    [| \ (b, x) → if b then Just x else Nothing |]
-}
derivingVector
    :: String   -- ^ Unique constructor suffix for the MVector and Vector data families
    -> Name     -- ^ Name of the class
    -> Name     -- ^ Name of the default type family
    -> Name     -- ^ Vec Rep
    -> TypeQ    -- ^ Quotation of the form @[t| /ctxt/ ⇒ src → rep |]@
    -> ExpQ     -- ^ Quotation of an expression of type @src → rep@
    -> ExpQ     -- ^ Quotation of an expression of type @rep → src@
    -> DecsQ    -- ^ Declarations to be spliced for the derived Unbox instance
derivingVector name cname famName vecRep argsQ toRepQ fromRepQ = do
    Common {..} <- common name
    toRep <- toRepQ
    fromRep <- fromRepQ
    a <- second (AppE toRep) <$> newPatExp "val"
    args <- argsQ
    (cxts, typ, rep) <- case args of
        ForallT _ cxts (ArrowT `AppT` typ `AppT` rep) -> return (cxts, typ, rep)
        ArrowT `AppT` typ `AppT` rep -> return ([], typ, rep)
        _ -> fail "Expecting a type of the form: cxts => typ -> rep"
    s <- newName "s"
    t <- newName "t"
    let newtypeMVector = NewtypeD [] mvName [PlainTV s, PlainTV t]
            (NormalC mvName [(NotStrict, (ConT ''G.Mutable `AppT` 
            (ConT famName `AppT` (ConT vecRep `AppT` VarT t)))
             `AppT` VarT s `AppT` (ConT vecRep `AppT` VarT t))]) []
    let mvCon = ConE mvName
    let instanceMVector = InstanceD cxts
            (ConT ''M.MVector `AppT` ConT mvName `AppT` typ) $ concat
            [ wrap 'M.basicLength           [mv]        id
            , wrap 'M.basicUnsafeSlice      [i, n, mv]  (AppE mvCon)
            , wrap 'M.basicOverlaps         [mv, mv']   id
            , wrap 'M.basicUnsafeNew        [n]         (liftE mvCon)
#if MIN_VERSION_vector(0,11,0)
            , wrap 'M.basicInitialize       [mv]        id
#endif
            , wrap 'M.basicUnsafeReplicate  [n, a]      (liftE mvCon)
            , wrap 'M.basicUnsafeRead       [mv, i]     (liftE fromRep)
            , wrap 'M.basicUnsafeWrite      [mv, i, a]  id
            , wrap 'M.basicClear            [mv]        id
            , wrap 'M.basicSet              [mv, a]     id
            , wrap 'M.basicUnsafeCopy       [mv, mv']   id
            , wrap 'M.basicUnsafeMove       [mv, mv']   id
            , wrap 'M.basicUnsafeGrow       [mv, n]     (liftE mvCon) ]

    -- let newtypeVector = NewtypeInstD [] ''Vector [typ]
    --         (NormalC vName [(NotStrict, ConT ''Vector `AppT` rep)]) []
    let newtypeVector = NewtypeD [] vName [PlainTV t]
            (NormalC vName [(NotStrict, ConT famName `AppT` (ConT vecRep `AppT` VarT t) `AppT` (ConT vecRep `AppT` VarT t))]) []
    let vCon  = ConE vName
    let instanceVector = InstanceD cxts
            (ConT ''G.Vector `AppT` ConT vName `AppT` typ) $ concat
            [ wrap 'G.basicUnsafeFreeze     [mv]        (liftE vCon)
            , wrap 'G.basicUnsafeThaw       [v]         (liftE mvCon)
            , wrap 'G.basicLength           [v]         id
            , wrap 'G.basicUnsafeSlice      [i, n, v]   (AppE vCon)
            , wrap 'G.basicUnsafeIndexM     [v, i]      (liftE fromRep)
            , wrap 'G.basicUnsafeCopy       [mv, v]     id
            , wrap 'G.elemseq               [v, a]      id ]

    return 
      [ -- InstanceD cxts (ConT cname `AppT` typ) []
        newtypeMVector, instanceMVector
      , newtypeVector, instanceVector 
      , TySynInstD ''G.Mutable (TySynEqn [ConT vName] (ConT mvName))
      ]

#undef __GLASGOW_HASKELL__
{-$usage

Writing @Unbox@ instances for new data types is tedious and formulaic. More
often than not, there is a straightforward mapping of the new type onto some
existing one already imbued with an @Unbox@ instance. The
<http://hackage.haskell.org/package/vector/docs/Data-Vector-Unboxed.html example>
from the @vector@ package represents @Complex a@ as pairs @(a, a)@. Using
'derivingVector', we can define the same instances much more succinctly:

>derivingVector "Complex"
>    [t| ∀ a. (Unbox a) ⇒ Complex a → (a, a) |]
>    [| \ (r :+ i) → (r, i) |]
>    [| \ (r, i) → r :+ i |]

Requires the @MultiParamTypeClasses@, @TemplateHaskell@, @TypeFamilies@ and
probably the @FlexibleInstances@ @LANGUAGE@ extensions. Note that GHC 7.4
(but not earlier nor later) needs the 'G.Vector' and 'M.MVector' class
method names to be in scope in order to define the appropriate instances:

>#if __GLASGOW_HASKELL__ == 704
>import qualified Data.Vector.Generic
>import qualified Data.Vector.Generic.Mutable
>#endif

Consult the <https://github.com/liyang/vector-th-unbox/blob/master/tests/sanity.hs sanity test>
for a working example.

-}


{-# OPTIONS_GHC -fprint-explicit-kinds #-}
{-# LANGUAGE PolyKinds #-}
-- https://github.com/input-output-hk/plutus/issues/4781
-- plutus-core makes life hard.
module Plutonomy.Constant (
    Constant (..),
    IsConstantType (..),
    IsConstantTypeI (..),
    constantFromPlutus,
    constantToPlutus,
    mkConstant,
) where

import Data.ByteString    (ByteString)
import Data.GADT.Compare  (GCompare (..), GEq (..), GOrdering (..))
import Data.Kind          (Type)
import Data.Text          (Text)
import Data.Type.Equality ((:~:) (..))
import PlutusCore.Data    (Data (..))
import PlutusCore.Default (DefaultUni (..), Esc, Some (..), ValueOf (..))

import qualified Prettyprinter as PP

-------------------------------------------------------------------------------
-- Simpler constants
-------------------------------------------------------------------------------

data Constant where
    MkConstant :: IsConstantType a -> a -> Constant

instance Eq Constant where
    MkConstant x x' == MkConstant y y' = case geq x y of
        Just Refl -> withEq x (x' == y')
        Nothing   -> False

instance Ord Constant where
    compare (MkConstant x x') (MkConstant y y') = case gcompare x y of
        GEQ -> withOrd x (compare x' y')
        GLT -> LT
        GGT -> GT

instance Show Constant where
    showsPrec d (MkConstant x x') = showParen (d > 10)
        $ showString "mkConstant "
        . withShow x (showsPrec 11 x')

instance PP.Pretty Constant where
    pretty = PP.pretty . constantToPlutus

data IsConstantType a where
    IsUnit       :: IsConstantType ()
    IsInteger    :: IsConstantType Integer
    IsByteString :: IsConstantType ByteString
    IsText       :: IsConstantType Text
    IsBool       :: IsConstantType Bool
    IsData       :: IsConstantType Data
    IsList       :: IsConstantType a -> IsConstantType [a]
    IsPair       :: IsConstantType a -> IsConstantType b -> IsConstantType (a, b)

class IsConstantTypeI a where isConstantType :: IsConstantType a
instance IsConstantTypeI ()         where isConstantType = IsUnit
instance IsConstantTypeI Integer    where isConstantType = IsInteger
instance IsConstantTypeI ByteString where isConstantType = IsByteString
instance IsConstantTypeI Text       where isConstantType = IsText
instance IsConstantTypeI Bool       where isConstantType = IsBool
instance IsConstantTypeI Data       where isConstantType = IsData
instance IsConstantTypeI a => IsConstantTypeI [a] where isConstantType = IsList isConstantType
instance (IsConstantTypeI a, IsConstantTypeI b) => IsConstantTypeI (a, b) where isConstantType = IsPair isConstantType isConstantType

mkConstant :: IsConstantTypeI a => a -> Constant
mkConstant = MkConstant isConstantType

instance GEq IsConstantType where
    geq IsUnit       IsUnit       = Just Refl
    geq IsUnit       _            = Nothing
    geq IsInteger    IsInteger    = Just Refl
    geq IsInteger    _            = Nothing
    geq IsByteString IsByteString = Just Refl
    geq IsByteString _            = Nothing
    geq IsText       IsText       = Just Refl
    geq IsText       _            = Nothing
    geq IsBool       IsBool       = Just Refl
    geq IsBool       _            = Nothing
    geq IsData       IsData       = Just Refl
    geq IsData       _            = Nothing
    geq (IsList x)   (IsList y)   = do
        Refl <- geq x y
        Just Refl
    geq (IsList _)   _            = Nothing
    geq (IsPair x y) (IsPair u v) = do
        Refl <- geq x u
        Refl <- geq y v
        Just Refl
    geq (IsPair _ _) _            = Nothing

instance GCompare IsConstantType where
    gcompare IsUnit       IsUnit       = GEQ
    gcompare IsUnit       _            = GLT
    gcompare _            IsUnit       = GGT
    gcompare IsInteger    IsInteger    = GEQ
    gcompare IsInteger    _            = GLT
    gcompare _            IsInteger    = GGT
    gcompare IsByteString IsByteString = GEQ
    gcompare IsByteString _            = GLT
    gcompare _            IsByteString = GGT
    gcompare IsText       IsText       = GEQ
    gcompare IsText       _            = GLT
    gcompare _            IsText       = GGT
    gcompare IsBool       IsBool       = GEQ
    gcompare IsBool       _            = GLT
    gcompare _            IsBool       = GGT
    gcompare IsData       IsData       = GEQ
    gcompare IsData       _            = GLT
    gcompare _            IsData       = GGT
    gcompare (IsList x)   (IsList y)   = case gcompare x y of
        GEQ -> GEQ
        GLT -> GLT
        GGT -> GGT
    gcompare (IsList _)   _            = GLT
    gcompare _            (IsList _)   = GGT
    gcompare (IsPair x y) (IsPair u v) = case gcompare x u of
        GLT -> GLT
        GGT -> GGT
        GEQ -> case gcompare y v of
            GEQ -> GEQ
            GLT -> GLT
            GGT -> GGT
    -- gcompare (IsPair _ _) _            = GLT
    -- gcompare _            (IsPair _ _) = GGT

withEq :: IsConstantType a -> (Eq a => r) -> r
withEq IsUnit       k = k
withEq IsInteger    k = k
withEq IsByteString k = k
withEq IsText       k = k
withEq IsBool       k = k
withEq IsData       k = k
withEq (IsList x)   k = withEq x k
withEq (IsPair x y) k = withEq x (withEq y k)

withOrd :: IsConstantType a -> (Ord a => r) -> r
withOrd IsUnit       k = k
withOrd IsInteger    k = k
withOrd IsByteString k = k
withOrd IsText       k = k
withOrd IsBool       k = k
withOrd IsData       k = k
withOrd (IsList x)   k = withOrd x k
withOrd (IsPair x y) k = withOrd x (withOrd y k)

withShow :: IsConstantType a -> (Show a => r) -> r
withShow IsUnit       k = k
withShow IsInteger    k = k
withShow IsByteString k = k
withShow IsText       k = k
withShow IsBool       k = k
withShow IsData       k = k
withShow (IsList x)   k = withShow x k
withShow (IsPair x y) k = withShow x (withShow y k)

-------------------------------------------------------------------------------
-- From plutus
-------------------------------------------------------------------------------

constantFromPlutus :: Some (ValueOf DefaultUni) -> Constant
constantFromPlutus (Some (ValueOf t x)) = MkConstant (isConstantTypeFromPlutus t) x

isConstantTypeFromPlutus :: forall (a :: Type). DefaultUni (Esc a) -> IsConstantType a
isConstantTypeFromPlutus DefaultUniUnit        = IsUnit
isConstantTypeFromPlutus DefaultUniInteger     = IsInteger
isConstantTypeFromPlutus DefaultUniByteString  = IsByteString
isConstantTypeFromPlutus DefaultUniString      = IsText
isConstantTypeFromPlutus DefaultUniBool        = IsBool
isConstantTypeFromPlutus DefaultUniData        = IsData
isConstantTypeFromPlutus (DefaultUniApply DefaultUniProtoList x)
    = IsList (isConstantTypeFromPlutus x)
isConstantTypeFromPlutus (DefaultUniApply (DefaultUniApply DefaultUniProtoPair x) y)
    = IsPair (isConstantTypeFromPlutus x) (isConstantTypeFromPlutus y)
isConstantTypeFromPlutus (DefaultUniApply (DefaultUniApply (DefaultUniApply f _) _) _)
    = noMoreTypeFunctions f

noMoreTypeFunctions :: DefaultUni (Esc (f :: a -> b -> c -> d)) -> any
noMoreTypeFunctions (f `DefaultUniApply` _) = noMoreTypeFunctions f

-------------------------------------------------------------------------------
-- to plutus
-------------------------------------------------------------------------------

constantToPlutus :: Constant -> Some (ValueOf DefaultUni)
constantToPlutus (MkConstant i x) = Some (ValueOf (isConstantTypeToPlutus i) x)

isConstantTypeToPlutus :: IsConstantType a -> DefaultUni (Esc a)
isConstantTypeToPlutus IsUnit       = DefaultUniUnit
isConstantTypeToPlutus IsInteger    = DefaultUniInteger
isConstantTypeToPlutus IsByteString = DefaultUniByteString
isConstantTypeToPlutus IsText       = DefaultUniString
isConstantTypeToPlutus IsBool       = DefaultUniBool
isConstantTypeToPlutus IsData       = DefaultUniData
isConstantTypeToPlutus (IsList x)   = DefaultUniApply DefaultUniProtoList (isConstantTypeToPlutus x)
isConstantTypeToPlutus (IsPair x y) = DefaultUniApply (DefaultUniApply DefaultUniProtoPair (isConstantTypeToPlutus x)) (isConstantTypeToPlutus y)

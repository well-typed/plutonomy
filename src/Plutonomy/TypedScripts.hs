module Plutonomy.TypedScripts (
    -- * Typed validator
    TypedValidator,
    mkTypedValidator,
    typedValidatorToPlutus,
    typedValidatorToRaw,
) where

import Ledger.Typed.Scripts (ValidatorType, WrappedValidatorType)
import PlutusTx.Code        (CompiledCode, applyCode)

import qualified Ledger.Typed.Scripts as Scripts
import qualified PlutusTx.Code        as PlutusTx
import qualified UntypedPlutusCore    as UPLC

import Plutonomy.Conversion
import Plutonomy.Raw

-------------------------------------------------------------------------------
-- Typed Validator
-------------------------------------------------------------------------------

data TypedValidator a = TypedValidator
    { _tvScript  :: CompiledCode (ValidatorType a)
    , _tvWrapper :: CompiledCode (ValidatorType a -> WrappedValidatorType)
    }

mkTypedValidator
    :: CompiledCode (ValidatorType a)
    -> CompiledCode (ValidatorType a -> WrappedValidatorType)
    -> TypedValidator a
mkTypedValidator = TypedValidator

-- | Convert plutonomy 'TypedValidator' to plutus 'Scripts.TypedValidator'.
typedValidatorToPlutus :: TypedValidator a -> Scripts.TypedValidator a
typedValidatorToPlutus (TypedValidator s w) = Scripts.mkTypedValidator s w

-- | Convert plutonomy 'TypedValidator' to plutonomy 'Term'.
typedValidatorToRaw :: TypedValidator a -> Raw n b
typedValidatorToRaw (TypedValidator s w) = case PlutusTx.getPlc c of
    UPLC.Program _ann _ver term -> fromUPLC term
  where
    c :: CompiledCode WrappedValidatorType
    c = w `applyCode` s

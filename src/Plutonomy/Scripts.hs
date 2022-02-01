-- | "Ledger.Scripts" / "Plutus.V1.Ledger.Api" like functionality.
module Plutonomy.Scripts (
    -- * Untyped validator
    Validator,
    mkValidatorScript,
    validatorToPlutus,
    validatorToRaw,
    -- * Minting policy
    MintingPolicy,
    mkMintingPolicyScript,
    mintingPolicyToPlutus,
    mintingPolicyToRaw,
) where

import PlutusTx      (BuiltinData)
import PlutusTx.Code (CompiledCode)

import qualified Plutus.V1.Ledger.Api as V1
import qualified PlutusTx.Code     as PlutusTx
import qualified UntypedPlutusCore as UPLC

import Plutonomy.Conversion
import Plutonomy.Raw

-------------------------------------------------------------------------------
-- Validator
-------------------------------------------------------------------------------

newtype Validator = Validator (CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ()))

mkValidatorScript
    :: CompiledCode (BuiltinData -> BuiltinData -> BuiltinData -> ())
    -> Validator
mkValidatorScript = Validator

validatorToPlutus :: Validator -> V1.Validator
validatorToPlutus (Validator w) = V1.mkValidatorScript w

validatorToRaw :: Validator -> Raw b n
validatorToRaw (Validator w) = case PlutusTx.getPlc w of
    UPLC.Program _ann _ver term -> fromUPLC term

-------------------------------------------------------------------------------
-- Minting policy
-------------------------------------------------------------------------------

newtype MintingPolicy = MintingPolicy (CompiledCode (BuiltinData -> BuiltinData -> ()))

mkMintingPolicyScript
    :: CompiledCode (BuiltinData -> BuiltinData -> ())
    -> MintingPolicy
mkMintingPolicyScript = MintingPolicy

mintingPolicyToPlutus :: MintingPolicy -> V1.MintingPolicy
mintingPolicyToPlutus (MintingPolicy w) = V1.mkMintingPolicyScript w

mintingPolicyToRaw :: MintingPolicy -> Raw b n
mintingPolicyToRaw (MintingPolicy w) = case PlutusTx.getPlc w of
    UPLC.Program _ann _ver term -> fromUPLC term

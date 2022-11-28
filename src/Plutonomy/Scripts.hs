{-# LANGUAGE CPP #-}
-- | "Ledger.Scripts" / "Plutus.V1.Ledger.Api" like functionality.
module Plutonomy.Scripts (
    -- * Untyped validator
    Validator,
    mkValidatorScript,
#if PLUTUS_VER <4
    validatorToPlutus,
#endif
    validatorToRaw,
    -- * Minting policy
    MintingPolicy,
    mkMintingPolicyScript,
#if PLUTUS_VER <4
    mintingPolicyToPlutus,
#endif
    mintingPolicyToRaw,
) where

import PlutusTx      (BuiltinData)
import PlutusTx.Code (CompiledCode)

import qualified PlutusTx.Code     as PlutusTx
import qualified UntypedPlutusCore as UPLC

#if PLUTUS_VER <4
import qualified Plutus.V1.Ledger.Api as V1
#endif

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

#if PLUTUS_VER <4
validatorToPlutus :: Validator -> V1.Validator
validatorToPlutus (Validator w) = V1.mkValidatorScript w
#endif

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

#if PLUTUS_VER <4
mintingPolicyToPlutus :: MintingPolicy -> V1.MintingPolicy
mintingPolicyToPlutus (MintingPolicy w) = V1.mkMintingPolicyScript w
#endif

mintingPolicyToRaw :: MintingPolicy -> Raw b n
mintingPolicyToRaw (MintingPolicy w) = case PlutusTx.getPlc w of
    UPLC.Program _ann _ver term -> fromUPLC term

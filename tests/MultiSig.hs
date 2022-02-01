{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell   #-}
-- | Multiple signatures contract
--
-- Similar to one in plutus-use-cases.
module MultiSig where

import Plutus.V1.Ledger.Api      (Validator)
import Plutus.V1.Ledger.Contexts (ScriptContext (scriptContextTxInfo), txSignedBy)
import Plutus.V1.Ledger.Crypto   (PubKeyHash)

import qualified PlutusTx
import qualified PlutusTx.Prelude as Pl

import qualified Plutonomy

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

data MultiSig = MultiSig
    { signatories      :: [PubKeyHash]
    -- ^ List of public keys of people who may sign the transaction
    , minNumSignatures :: Integer
    -- ^ Minimum number of signatures required to unlock
    --   the output (should not exceed @length signatories@)
    } deriving (Show)

PlutusTx.makeLift ''MultiSig

-------------------------------------------------------------------------------
-- on-chain
-------------------------------------------------------------------------------

validate :: MultiSig -> Pl.BuiltinData -> Pl.BuiltinData -> Pl.BuiltinData -> ()
validate ms _datum _redeemer ctx =
    if validate' ms (PlutusTx.unsafeFromBuiltinData ctx)
    then ()
    else Pl.error ()

validate' :: MultiSig -> ScriptContext -> Bool
validate' MultiSig{signatories = sigs, minNumSignatures = needed} p =
    let present :: Integer
        present = Pl.length (Pl.filter (txSignedBy (scriptContextTxInfo p)) sigs)

    in Pl.traceIfFalse "E1" (present Pl.>= needed)

-------------------------------------------------------------------------------
-- script compilation
-------------------------------------------------------------------------------

-- | Plutonomy validator (which contains the script with names)
validator' :: MultiSig -> Plutonomy.Validator
validator' ms = Plutonomy.mkValidatorScript
    ($$(PlutusTx.compile [|| validate ||]) `PlutusTx.applyCode` PlutusTx.liftCode ms)

-- | Plutus validator
validator :: MultiSig -> Validator
validator = Plutonomy.optimizeUPLC . Plutonomy.validatorToPlutus . validator'

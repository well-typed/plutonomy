{-# LANGUAGE CPP               #-}
{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

#if PLUTUS_VER <4
import Plutus.V1.Ledger.Crypto (PubKeyHash (..))
#else
import PlutusLedgerApi.V1.Crypto (PubKeyHash (..))
#endif

import Test.Tasty (defaultMain, testGroup)

import Plutonomy      (validatorToRaw)
import Plutonomy.Test

import qualified MultiSig

main :: IO ()
main = defaultMain $ testGroup "plutonomy"
    [ plutonomyTests TestOptions
        { toName        = "multisig"

#if PLUTUS_VER == 1
        , toUnoptSize   = (2928,2532)
#elif PLUTUS_VER == 2
        , toUnoptSize   = (2923,2432)
#elif PLUTUS_VER == 3
        , toUnoptSize   = (2651,2210)
#elif PLUTUS_VER == 4
        , toUnoptSize   = (2714,2293)
#else
        , toUnoptSize   = (0,0)
#endif

#if PLUTUS_VER == 4
        , toOptSize     = (1873,1664) -- 75% of original
        , toAggSize     = (1875,1634)

#elif PLUTUS_VER == 3
        -- plutus-tx makes our life harder: https://github.com/input-output-hk/plutus/issues/4578
        , toOptSize     = (1870,1661) -- 75% of original
        , toAggSize     = (1872,1632)
#else
        , toOptSize     = (1802,1611) -- 66% of original
        , toAggSize     = (1804,1582)
#endif

        , toTerm        = validatorToRaw $ MultiSig.validator' multisigParams
#if PLUTUS_VER == 1
        , toFixturesDir = "fixtures-1"
#elif PLUTUS_VER == 2
        , toFixturesDir = "fixtures-2"
#elif PLUTUS_VER == 3
        , toFixturesDir = "fixtures-3"
#elif PLUTUS_VER == 4
        , toFixturesDir = "fixtures-4"
#else
        , toFixturesDir = error "Invalid configuration"
#endif
        }
    ]

multisigParams :: MultiSig.MultiSig
multisigParams = MultiSig.MultiSig
    { MultiSig.signatories =
        [ PubKeyHash "some-string-which-is-28-long"
        , PubKeyHash "s0me-string-which-is-28-long"
        , PubKeyHash "some-string-which-is-28-l0ng"
        ]
    , MultiSig.minNumSignatures = 2
    }

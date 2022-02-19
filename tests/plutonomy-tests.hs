{-# LANGUAGE OverloadedStrings #-}
module Main (main) where

import Plutus.V1.Ledger.Crypto (PubKeyHash (..))
import Test.Tasty              (defaultMain, testGroup)

import Plutonomy      (validatorToRaw)
import Plutonomy.Test

import qualified MultiSig

main :: IO ()
main = defaultMain $ testGroup "plutonomy"
    [ plutonomyTests TestOptions
        { toName        = "multisig"
        , toUnoptSize   = (2928,2532)
        , toOptSize     = (1900,1653) -- 65% of original
        , toAggSize     = (1902,1623)
        , toTerm        = validatorToRaw $ MultiSig.validator' multisigParams
        , toFixturesDir = "fixtures"
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
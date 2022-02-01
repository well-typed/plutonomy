-- | Test utilities.
module Plutonomy.Test (
    TestOptions (..),
    plutonomyTests,
) where

import Data.Strict       (toLazy)
import System.FilePath   ((</>))
import Test.Tasty        (TestTree, testGroup)
import Test.Tasty.Golden (goldenVsString)
import Test.Tasty.HUnit  (testCase, (@?=))

import qualified Data.Text.Encoding as TE
import qualified UntypedPlutusCore  as UPLC

import Plutonomy (ClosedRaw, aggressiveOptimizerOptions, optimizeUPLC, optimizeUPLCWith, statsUPLC, textUPLC, toUPLC)
import Plutonomy.PlutusExtras

data TestOptions x = TestOptions
    { toName        :: String              -- ^ term name
    , toTerm        :: ClosedRaw           -- ^ term itself
    , toUnoptSize   :: (Integer, Integer)  -- ^ expected original size (ast nodes, bytes)
    , toOptSize     :: (Integer, Integer)  -- ^ optimized size
    , toAggSize     :: (Integer, Integer)  -- ^ aggressively optimized size
    , toFixturesDir :: FilePath            -- ^ directory for term dumps
    }

-- | Test @plutonomy@ on a term.
--
-- Check original and optimized sizes and golden test the optimization results.
plutonomyTests :: TestOptions x -> TestTree
plutonomyTests to = testGroup (toName to)
    [ testGroup "Script size"
        [ testCase "original" $ do
            statsUPLC (renameToDeBruijn orgValidator) @?= toUnoptSize to
        , testCase "optimized" $ do
            statsUPLC (renameToDeBruijn optValidator) @?= toOptSize to
        , testCase "aggressive" $ do
            statsUPLC (renameToDeBruijn aggValidator) @?= toAggSize to
        ]

    , testGroup "Dumps"
        [ goldenVsString "original" (toFixturesDir to </> (toName to ++ "-original.txt")) $ do
            return $ toLazy $ TE.encodeUtf8 $ textUPLC orgValidator

        , goldenVsString "optimized" (toFixturesDir to </> (toName to ++ "-optimized.txt")) $ do
            return $ toLazy $ TE.encodeUtf8 $ textUPLC optValidator

        , goldenVsString "aggressive" (toFixturesDir to </> (toName to ++ "-aggressive.txt")) $ do
            return $ toLazy $ TE.encodeUtf8 $ textUPLC aggValidator
        ]
    ]
  where
    orgValidator = toUPLC (toTerm to) :: UPLC.Term UPLC.NamedDeBruijn UPLC.DefaultUni UPLC.DefaultFun ()
    optValidator = optimizeUPLC orgValidator
    aggValidator = optimizeUPLCWith aggressiveOptimizerOptions orgValidator


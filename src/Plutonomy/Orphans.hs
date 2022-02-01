{-# LANGUAGE CPP                  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeApplications     #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Plutonomy.Orphans () where

#if PLUTUS_VER <2
import Data.GADT.Compare    (GCompare (..), GOrdering (..))
import Data.GADT.Compare.TH (deriveGCompare)
import Data.Proxy           (Proxy (..))
import PlutusCore.Default   (Closed, DefaultUni, Everywhere, ValueOf (..), bring)

-- https://github.com/input-output-hk/plutus-apps/issues/75
deriveGCompare ''DefaultUni

instance (GCompare uni, Closed uni, uni `Everywhere` Ord, uni `Everywhere` Eq) => GCompare (ValueOf uni) where
    ValueOf uni1 x1 `gcompare` ValueOf uni2 x2 =
        case uni1 `gcompare` uni2 of
            GLT -> GLT
            GGT -> GGT
            GEQ -> do
                bring (Proxy @Ord) uni1 $ case compare x1 x2 of
                    EQ -> GEQ
                    LT -> GLT
                    GT -> GGT

#endif

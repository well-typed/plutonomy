{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators     #-}
module Plutonomy.Known (
    Known (..),
    known,
    knownRaw,
    isKnown,
    pattern Known,
    knownName,
    -- * Raws
    -- ** One argument functions
    pattern RawId,
    pattern RawDelayId,
    pattern RawDelayDelayId,
    -- ** Two argument functions
    pattern RawConst,
    pattern RawFlipConst,
    pattern RawTrue,
    pattern RawFalse,
    pattern RawDelayTrue,
    pattern RawDelayFalse,
    -- ** Three argument functions
    pattern RawFstOf3, pattern RawSndOf3, pattern RawTrdOf3,
    pattern RawEQ, pattern RawGT, pattern RawLT,
    pattern RawDelayEQ, pattern RawDelayGT, pattern RawDelayLT,
    -- ** Built-ins
    pattern RawTT,
    pattern RawIFE,
    pattern RawTrace,
    pattern RawDelayError,
    -- ** Fixed point
    pattern RawFix,
    pattern RawZ,
) where

import PlutusCore.Default (DefaultFun (..), DefaultUni (..), Some (..), ValueOf (..))
import Subst              (Var (..))

import Plutonomy.Name
import Plutonomy.Raw

-- $setup
-- >>> import Plutonomy
-- >>> import Subst
-- >>> import Data.Text (Text)
-- >>> import Control.Monad (forM_)
-- >>> import qualified Prettyprinter as PP
-- >>> let pp t = prettyRaw PP.pretty (t :: Raw Text Z)

-------------------------------------------------------------------------------
-- Known
-------------------------------------------------------------------------------

-- | Known terms.
--
-- === One argument functions
--
-- Identity function and its delayed forms:
--
-- * @\\ x -> x@ is 'RawId'
--
-- * @\\ ~ y -> y@ is 'RawDelayId'
--
-- * @\\ ~ ~ z -> z@ is 'RawDelayDelayId'
--
-- === Two argument functions
--
-- Const function and its flipped, and their delayed forms:
--
-- * @\\ x y -> x@ is 'RawConst'
--
-- * @\\ x y -> y@ is 'RawFlipConst'
--
-- * @\\ ~ x y -> y@ is 'RawFalse'
--
-- * @\\ ~ x y -> x@ is 'RawTrue'
--
-- * @\\ ~ ~ x y -> y@ is 'RawDelayFalse'
--
-- * @\\ ~ ~ x y -> x@ is 'RawDelayTrue'
--
-- === Three argument functions
--
-- The same as above but for three argument functions:
--
-- * @\\ x y z -> x@ is 'RawFstOf3'
--
-- * @\\ x y z -> y@ is 'RawSndOf3'
--
-- * @\\ x y z -> z@ is 'RawTrdOf3'
--
-- * @\\ ~ x y z -> x@ is 'RawEQ' (note: I'm not sure why Plutus compiles them in this order).
--
-- * @\\ ~ x y z -> y@ is 'RawGT'
--
-- * @\\ ~ x y z -> z@ is 'RawLT'
--
-- * @\\ ~ ~ x y z -> x@ is 'RawDelayEQ'
--
-- * @\\ ~ ~ x y z -> y@ is 'RawDelayGT'
--
-- * @\\ ~ ~ x y z -> z@ is 'RawDelayLT'
--
-- === Builtin and Constants
--
-- * @ifThenElse#@, @()#@, @trace#@, @\\~ -> ERROR@
--
data Known
    = KnownId
    | KnownDelayId
    | KnownDelayDelayId
    | KnownConst
    | KnownFlipConst
    | KnownTrue
    | KnownFalse
    | KnownDelayTrue
    | KnownDelayFalse
    | KnownFstOf3
    | KnownSndOf3
    | KnownTrdOf3
    | KnownEQ
    | KnownGT
    | KnownLT
    | KnownDelayEQ
    | KnownDelayGT
    | KnownDelayLT
    | KnownIFE
    | KnownTT
    | KnownTrace
    | KnownDelayError
    | KnownFix
    | KnownZ
  deriving (Eq, Ord, Enum, Bounded)

-- |
--
-- >>> forM_ known $ \k -> print $ pp $ knownRaw k
-- \ x -> x
-- \ ~ y -> y
-- \ ~ ~ z -> z
-- \ u1 v1 -> u1
-- \ u2 v2 -> v2
-- \ ~ true1 false1 -> true1
-- \ ~ true2 false2 -> false2
-- \ ~ ~ true3 false3 -> true3
-- \ ~ ~ true4 false4 -> false4
-- \ m1 n1 p1 -> m1
-- \ m2 n2 p2 -> n2
-- \ m3 n3 p3 -> p3
-- \ ~ m4 n4 p4 -> m4
-- \ ~ m5 n5 p5 -> n5
-- \ ~ m6 n6 p6 -> p6
-- \ ~ ~ m7 n7 p7 -> m7
-- \ ~ ~ m8 n8 p8 -> n8
-- \ ~ ~ m9 n9 p9 -> p9
-- ifThenElse#
-- ()#
-- trace#
-- \ ~ -> ERROR
-- \ f -> let* rec = \ rec0 arg -> f (rec0 rec0) arg in rec rec
-- \ f -> let* x = \ y -> f (\ u -> y y u) in f (\ v -> x x v)
--
known :: [Known]
known = [minBound .. maxBound]

knownName :: Known -> Name
knownName KnownId           = "id"
knownName KnownDelayId      = "~id"
knownName KnownDelayDelayId = "~~id"
knownName KnownConst        = "const"
knownName KnownFlipConst    = "flipConst"
knownName KnownTrue         = "True"
knownName KnownFalse        = "False"
knownName KnownDelayTrue    = "~True"
knownName KnownDelayFalse   = "~False"
knownName KnownFstOf3       = "fstOf3"
knownName KnownSndOf3       = "sndOf3"
knownName KnownTrdOf3       = "trdOf3"
knownName KnownEQ           = "EQ"
knownName KnownGT           = "GT"
knownName KnownLT           = "LT"
knownName KnownDelayEQ      = "~EQ"
knownName KnownDelayGT      = "~GT"
knownName KnownDelayLT      = "~LT"
knownName KnownIFE          = "ifThenElse"
knownName KnownTT           = "tt"
knownName KnownTrace        = "trace"
knownName KnownDelayError   = "~ERROR"
knownName KnownFix          = "fix"
knownName KnownZ            = "zComb"

knownRaw :: Known -> Raw a n
knownRaw KnownId           = RawId "x"
knownRaw KnownDelayId      = RawDelayId "y"
knownRaw KnownDelayDelayId = RawDelayDelayId "z"
knownRaw KnownConst        = RawConst "u1" "v1"
knownRaw KnownFlipConst    = RawFlipConst "u2" "v2"
knownRaw KnownTrue         = RawTrue       "true1" "false1"
knownRaw KnownFalse        = RawFalse      "true2" "false2"
knownRaw KnownDelayTrue    = RawDelayTrue  "true3" "false3"
knownRaw KnownDelayFalse   = RawDelayFalse "true4" "false4"
knownRaw KnownFstOf3       = RawFstOf3  "m1" "n1" "p1"
knownRaw KnownSndOf3       = RawSndOf3  "m2" "n2" "p2"
knownRaw KnownTrdOf3       = RawTrdOf3  "m3" "n3" "p3"
knownRaw KnownEQ           = RawEQ      "m4" "n4" "p4"
knownRaw KnownGT           = RawGT      "m5" "n5" "p5"
knownRaw KnownLT           = RawLT      "m6" "n6" "p6"
knownRaw KnownDelayEQ      = RawDelayEQ "m7" "n7" "p7"
knownRaw KnownDelayGT      = RawDelayGT "m8" "n8" "p8"
knownRaw KnownDelayLT      = RawDelayLT "m9" "n9" "p9"
knownRaw KnownIFE          = RawIFE
knownRaw KnownTT           = RawTT
knownRaw KnownTrace        = RawTrace
knownRaw KnownDelayError   = RawDelayError
knownRaw KnownFix          = RawFix "f" "rec" "rec0" "arg"
knownRaw KnownZ            = RawZ "f" "x" "v" "y" "u"

isKnown :: Raw a n -> Maybe Known
isKnown RawId {}           = Just KnownId
isKnown RawDelayId {}      = Just KnownDelayId
isKnown RawDelayDelayId {} = Just KnownDelayDelayId
isKnown RawConst {}        = Just KnownConst
isKnown RawFlipConst {}    = Just KnownFlipConst
isKnown RawTrue {}         = Just KnownTrue
isKnown RawFalse {}        = Just KnownFalse
isKnown RawDelayTrue {}    = Just KnownDelayTrue
isKnown RawDelayFalse {}   = Just KnownDelayFalse
isKnown RawFstOf3  {}      = Just KnownFstOf3
isKnown RawSndOf3  {}      = Just KnownSndOf3
isKnown RawTrdOf3  {}      = Just KnownTrdOf3
isKnown RawEQ      {}      = Just KnownEQ
isKnown RawGT      {}      = Just KnownGT
isKnown RawLT      {}      = Just KnownLT
isKnown RawDelayEQ {}      = Just KnownDelayEQ
isKnown RawDelayGT {}      = Just KnownDelayGT
isKnown RawDelayLT {}      = Just KnownDelayLT
isKnown RawIFE             = Just KnownIFE
isKnown RawTT              = Just KnownTT
isKnown RawTrace           = Just KnownTrace
isKnown RawDelayError      = Just KnownDelayError
isKnown RawFix {}          = Just KnownFix
isKnown RawZ {}            = Just KnownZ
isKnown _                  = Nothing

pattern Known :: Known -> Raw (Either Known a) n
pattern Known k = Free (Left k)

-------------------------------------------------------------------------------
-- Raws
-------------------------------------------------------------------------------

pattern RawFalse :: Name -> Name -> Raw a n
pattern RawFalse ctrue cfalse = Delay (Lam ctrue (Lam cfalse (Var VZ)))

pattern RawTrue :: Name -> Name -> Raw a n
pattern RawTrue ctrue cfalse = Delay (Lam ctrue (Lam cfalse (Var (VS VZ))))

pattern RawIFE :: Raw a n
pattern RawIFE = Builtin IfThenElse

pattern RawTT :: Raw a n
pattern RawTT = Constant (Some (ValueOf DefaultUniUnit ()))

pattern RawTrace :: Raw a n
pattern RawTrace = Builtin Trace

pattern RawId :: Name -> Raw a n
pattern RawId x = Lam x (Var VZ)

pattern RawDelayId :: Name -> Raw a n
pattern RawDelayId y = Delay (RawId y)

pattern RawDelayDelayId :: Name -> Raw a n
pattern RawDelayDelayId y = Delay (RawDelayId y)

pattern RawConst :: Name -> Name -> Raw a n
pattern RawConst u v = Lam u (Lam v (Var (VS VZ)))

pattern RawFlipConst :: Name -> Name -> Raw a n
pattern RawFlipConst k l = Lam k (Lam l (Var VZ))

pattern RawDelayTrue :: Name -> Name -> Raw a n
pattern RawDelayTrue ctrue cfalse = Delay (RawTrue ctrue cfalse)

pattern RawDelayFalse :: Name -> Name -> Raw a n
pattern RawDelayFalse ctrue cfalse = Delay (RawFalse ctrue cfalse)

pattern RawDelayError :: Raw a n
pattern RawDelayError = Delay Error

pattern RawFstOf3 :: Name -> Name -> Name -> Raw a n
pattern RawFstOf3 m n p = Lam m (Lam n (Lam p Var2))

pattern RawSndOf3 :: Name -> Name -> Name -> Raw a n
pattern RawSndOf3 m n p = Lam m (Lam n (Lam p Var1))

pattern RawTrdOf3 :: Name -> Name -> Name -> Raw a n
pattern RawTrdOf3 m n p = Lam m (Lam n (Lam p Var0))

pattern RawEQ :: Name -> Name -> Name -> Raw a n
pattern RawEQ m n p = Delay (RawFstOf3 m n p)

pattern RawGT :: Name -> Name -> Name -> Raw a n
pattern RawGT m n p = Delay (RawSndOf3 m n p)

pattern RawLT :: Name -> Name -> Name -> Raw a n
pattern RawLT m n p = Delay (RawTrdOf3 m n p)

pattern RawDelayEQ :: Name -> Name -> Name -> Raw a n
pattern RawDelayEQ m n p = Delay (RawEQ m n p)

pattern RawDelayGT :: Name -> Name -> Name -> Raw a n
pattern RawDelayGT m n p = Delay (RawGT m n p)

pattern RawDelayLT :: Name -> Name -> Name -> Raw a n
pattern RawDelayLT m n p = Delay (RawLT m n p)

pattern RawFix :: Name -> Name -> Name -> Name -> Raw a n
pattern RawFix f s s0 x
    = Lam f (Let s (Lam s0 (Lam x (Var2 :@ (Var1 :@ Var1) :@ Var0))) (Var0 :@ Var0))

pattern RawZ :: Name -> Name -> Name -> Name -> Name -> Raw a n
pattern RawZ f x v y u = Lam f
    (Let x (Lam y (Var1 :@ Lam u (Var1 :@ Var1 :@ Var0)))
           (Var1 :@ Lam v (Var1 :@ Var1 :@ Var0)))


module Plutonomy.Optimize (
    -- * Optimizer
    optimize,
    optimizeWith,
    -- ** Optimizer options
    OptimizerOptions (..),
    TraceRewrite (..),
    IfeRewrite (..),
    defaultOptimizerOptions,
    aggressiveOptimizerOptions,
) where

import Control.Category ((>>>))
import Data.List        (foldl')
import Numeric.Natural  (Natural)

import Plutonomy.MissingH
import Plutonomy.Raw
import Plutonomy.Raw.Rewrite
import Plutonomy.Raw.Transform

import qualified Plutonomy.Hereditary           as H
import qualified Plutonomy.Hereditary.Rewrite   as H
import qualified Plutonomy.Hereditary.Transform as H

-------------------------------------------------------------------------------
-- Options
-------------------------------------------------------------------------------

-- | Optimizer options.
--
data OptimizerOptions = OptimizerOptions
    { ooOptimizerRounds  :: Natural
      -- ^ How many optimizer rounds to run.
      --
      -- There is always one round in addition.

    , ooPreInlineConsts  :: Bool
      -- ^ Inline constants in a pre-phase.
      --
      -- Then the common subexpression eliminator will more opportunities.
      --
      -- See 'inlineConstants'.

    , ooInlineUsedOnce   :: Bool
      -- ^ Inline (value) bindings which are used at most once.

    , ooInlineSaturated  :: Bool
      -- ^ Inline saturated applications of (cheap) functions.
      --
      -- See 'inlineSaturated'.

    , ooSplitDelay       :: Bool
      -- ^ TODO: whether to float only values or also forced things
      --
      -- See 'splitDelay'.

    , ooEtaForce         :: Bool
      -- ^
      --
      -- See 'etaForce'.

    , ooEtaFun           :: Bool
      -- ^
      --
      -- See 'etaFun'.

    , ooFloatOutLambda   :: Bool
      -- ^
      --
      -- See 'floatOutLambda'.

    , ooFloatOutDelay    :: Bool
      -- ^
      --
      -- See 'floatOutDelay'.

    , ooFloatOutAppArg   :: Maybe FloatOutAppArg
      -- ^
      --
      -- See 'floatOutAppArg'.

    , ooIfLambda         :: Bool
      -- ^
      --
      -- See 'ifLambda'.

    , ooAppError         :: Maybe AppError
      --
      --
      -- See 'appError'.

    , ooCombineBindings  :: Bool
      --
      --
      -- ^ See 'commonBindings'

    , ooKnownRewrites    :: Bool
      -- ^ Whether to perform any known rewrites.
      --
      --

    , ooTraceRewrite     :: Maybe TraceRewrite
      -- ^ Rewrite @trace@ applications.

    , ooIfeRewrite       :: Maybe IfeRewrite
      -- ^ Rewrite @ifThenElse@ applications.

    , ooCommuteEquals    :: Bool
      -- ^ Commute builtin equals to have constant argument first
      --
      -- See 'commEquals'.

    , ooLetZero          :: Bool
      -- ^
      --
      -- See 'letZero'

    , ooCSE              :: Bool
      -- ^ Common subexpression elimination.

    , ooFloatIn          :: Bool
      -- ^ Float in bindings. Performed after main optimizations loops
      --
      -- See 'floatIn'.

    }
  deriving (Eq, Show)

-- | Default optimizer options.
defaultOptimizerOptions :: OptimizerOptions
defaultOptimizerOptions = OptimizerOptions
    { ooOptimizerRounds = 2
    , ooPreInlineConsts = True
    , ooInlineUsedOnce  = True
    , ooInlineSaturated = True
    , ooSplitDelay      = True
    , ooEtaForce        = True
    , ooEtaFun          = True
    , ooFloatOutLambda  = True
    , ooFloatOutDelay   = True
    , ooFloatOutAppArg  = Just FloatOutAppArgValue
    , ooIfLambda        = True
    , ooCombineBindings = True
    , ooKnownRewrites   = True
    , ooTraceRewrite    = Just TraceRewrite
    , ooIfeRewrite      = Just IfeRewrite
    , ooAppError        = Just AppErrorValue
    , ooCommuteEquals   = True
    , ooLetZero         = True
    , ooCSE             = True
    , ooFloatIn         = True
    }

-- | Aggressive optimizer options which may not preserve semantics.
aggressiveOptimizerOptions :: OptimizerOptions
aggressiveOptimizerOptions = defaultOptimizerOptions
    { ooOptimizerRounds = 2
    , ooTraceRewrite    = Just TraceRemove
    , ooIfeRewrite      = Just IfeRewriteMore
    , ooAppError        = Just AppErrorAll
    , ooFloatOutAppArg  = Just FloatOutAppArgAll
    }

-- | Optimize 'Term' using 'defaultOptimizerOptions'.
optimize :: Ord a => Raw a n -> Raw a n
optimize = optimizeWith defaultOptimizerOptions

-- | Optimize 'Term' using given 'OptimizerOptions'.
optimizeWith :: Ord a => OptimizerOptions -> Raw a n -> Raw a n
optimizeWith oo = H.fromRaw >>> pipeline >>> H.toRaw
  where
    enable True  xs = xs
    enable False _ = []

    pipeline :: Ord a => H.Term a n -> H.Term a n
    pipeline = foldl' (>>>) id (
        -- add prelude (only if we are going to combine bindings)
        [ H.toRaw >>> renameLets >>> prelude >>> H.fromRaw | ooCombineBindings oo ] ++
        -- inline constants
        [ H.rewrite H.inlineConstants | ooPreInlineConsts oo ] ++
        -- loop optimizer
        [ loop | _ <- [1 .. ooOptimizerRounds oo] ] ++
        -- apply known rewrites
        [ H.toRaw >>> knownRewrites (ooTraceRewrite oo) (ooIfeRewrite oo) >>> H.fromRaw | ooKnownRewrites oo ] ++
        -- Float in bindings so splitDelay and inlineSaturated could remove more delaying
        enable (ooFloatIn oo) [ H.toRaw >>> floatIn' >>> H.fromRaw
                              , H.splitDelay'
                              , fixedpoint (H.inlineSaturated' (- 2)) ] ++
        -- common subexpression elimination
        [ H.toRaw >>> cse 5 >>> H.fromRaw | ooCSE oo ] ++
        -- last loop, we don't float out bindings anymore.
        [ loop
        -- and last cleanup
        , H.toRaw >>> fixedpoint (simplify . rewriteWithBindings cleanupRewrites) >>> H.fromRaw
        ])

    loop :: Ord a => H.Term a n -> H.Term a n
    loop  = foldl' (>>>) id $
        -- Float delayed definitions, so their forcings are saturated
        [ H.splitDelay' | ooSplitDelay oo ] ++
        -- Inline saturated
        [ fixedpoint (H.inlineSaturated' 0) | ooInlineSaturated oo ] ++
        -- combine common bindings
        [ H.commonBindings | ooCombineBindings oo ] ++
        -- Propagate errors, ..., inline used once
        [ fixedpoint (H.rewriteWithDefinitions simpleRewrites) ]

    simpleRewrites :: H.Definitions a n -> H.Term a n -> Maybe (H.Term a n)
    simpleRewrites = foldl' (\//) (\_ _ -> Nothing) $
        [ H.inlineUsedOnce    | ooInlineUsedOnce oo ] ++
        [ const H.letZero     | ooLetZero oo ] ++
        [ H.appError x        | Just x <- [ ooAppError oo ] ] ++
        [ H.etaForce          | ooEtaForce oo ] ++
        [ H.etaFun            | ooEtaFun oo ] ++
        [ H.ifLambda          | ooIfLambda oo ] ++
        [ H.floatOutLambda    | ooFloatOutLambda oo ] ++
        [ H.floatOutAppArg x  | Just x <- [ ooFloatOutAppArg oo ] ] ++
        [ H.floatOutDelay     | ooFloatOutDelay oo ] ++
        [ const H.commBuiltin | ooCommuteEquals oo ]

    cleanupRewrites :: Ord a => Bindings a n -> Raw a n -> Maybe (Raw a n)
    cleanupRewrites = foldl' (\//) (\_ _ -> Nothing) $
        [ inlineUsedOnce    | ooInlineUsedOnce oo ] ++
        [ inlineSaturated 0 | ooInlineSaturated oo ] ++
        [ floatOutLambda    | ooFloatOutLambda oo ] ++
        [ floatOutAppArg x  | Just x <- [ ooFloatOutAppArg oo ] ] ++
        [ floatOutDelay     | ooFloatOutDelay oo ]

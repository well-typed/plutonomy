{-# LANGUAGE CPP #-}
-- | Utilities to work on 'Script's,
-- etc things containing Untyped Plutus Core.
module Plutonomy.UPLC (
    HasUPLC (..),
    optimizeUPLC,
    optimizeUPLCWith,
    dumpUPLC,
    textUPLC,
    textUPLC',
    statsUPLC,
    viewUPLC,
) where

import Control.Lens              (Lens', lens, over, view)
import Data.Text                 (Text)
import Plutus.V1.Ledger.Api      (MintingPolicy (..), Validator (..))
import Plutus.V1.Ledger.Scripts  (Script (..))
import PlutusCore.Default        (DefaultFun, DefaultUni)
import Prettyprinter.Render.Text (renderIO, renderStrict)
import System.IO                 (stdout)

#ifdef VERSION_plutus_ledger
import Data.Coerce                     (coerce)
import Ledger.Typed.Scripts.Validators (TypedValidator, unsafeMkTypedValidator, validatorScript)
#endif

import qualified PlutusTx.Code     as PlutusTx
import qualified Prettyprinter     as PP
import qualified UntypedPlutusCore as UPLC

import Plutonomy.Conversion
import Plutonomy.Optimize
import Plutonomy.PlutusExtras
import Plutonomy.Pretty
import Plutonomy.Raw.Transform (simplify)

-------------------------------------------------------------------------------
-- Things with HasUPLC
-------------------------------------------------------------------------------

-- | Things with untyped plutus core term in them.
class HasUPLC a where
    uplc :: Lens' a (UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ())

instance (HasUPLCTerm name, uni ~ DefaultUni, fun ~ DefaultFun, ann ~ ()) => HasUPLC (UPLC.Term name uni fun ann) where
    uplc = uplcTerm

instance (HasUPLCTerm name, uni ~ DefaultUni, fun ~ DefaultFun, ann ~ ()) => HasUPLC (UPLC.Program name uni fun ann) where
    uplc f (UPLC.Program ann ver t) = UPLC.Program ann ver <$> uplc f t

-- | This instance removes PIR representation.
instance (uni ~ DefaultUni, fun ~ DefaultFun) => HasUPLC (PlutusTx.CompiledCodeIn uni fun a) where
    uplc = lens getter setter where
        getter
            :: PlutusTx.CompiledCodeIn DefaultUni DefaultFun a
            -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
        getter c = case PlutusTx.getPlc c of UPLC.Program _ann _ver term -> term

        setter
            :: PlutusTx.CompiledCodeIn DefaultUni DefaultFun a
            -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
            -> PlutusTx.CompiledCodeIn DefaultUni DefaultFun a
        setter c term = case PlutusTx.getPlc c of
            UPLC.Program ann ver _term -> PlutusTx.DeserializedCode
                (UPLC.Program ann ver term)
                Nothing -- PIR is gone.
#if PLUTUS_VER >=2
                mempty  -- coverage index is gone
#endif

instance HasUPLC Validator where
    uplc f (Validator s) = Validator <$> uplc f s

instance HasUPLC MintingPolicy where
    uplc f (MintingPolicy s) = MintingPolicy <$> uplc f s

instance HasUPLC Script where
    uplc f (Script s) = Script <$> uplc f s

-- https://github.com/input-output-hk/plutus-apps/issues/74
#ifdef VERSION_plutus_ledger
instance HasUPLC (TypedValidator a) where
    uplc f v = coerce . unsafeMkTypedValidator <$> uplc f (validatorScript v)
#endif

-------------------------------------------------------------------------------
-- HasUPLCTerm (renaming terms)
-------------------------------------------------------------------------------

class HasUPLCTerm name where
    uplcTerm :: Lens' (UPLC.Term name DefaultUni DefaultFun ()) (UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ())

instance HasUPLCTerm UPLC.NamedDeBruijn where
    uplcTerm = id

instance HasUPLCTerm UPLC.DeBruijn where
    uplcTerm f term = renameToDeBruijn <$> f (renameFromDeBruijn term)

-------------------------------------------------------------------------------
-- Utilities
-------------------------------------------------------------------------------

-- | Optimize the untyped plutus core.
optimizeUPLC :: HasUPLC a => a -> a
optimizeUPLC = over uplc (toUPLC . optimize . fromUPLC)

-- | Optimize the untyped plutus core.
optimizeUPLCWith :: HasUPLC a => OptimizerOptions -> a -> a
optimizeUPLCWith oo = over uplc (toUPLC . optimizeWith oo . fromUPLC)

-- | Dump UPLC to 'stdout' using Haskell-like syntax.
dumpUPLC :: HasUPLC a => a -> IO ()
dumpUPLC = putDocW dumpWidth .  toDoc

-- | Convert UPLC to 'Text' representation using Haskell-like syntax.
textUPLC :: HasUPLC a => a -> Text
textUPLC = putDocT dumpWidth . toDoc

-- | 'textUPLC' with configurable width.
textUPLC' :: HasUPLC a => Int -> a -> Text
textUPLC' w = putDocT w . toDoc

-- | Return size statistics of UPLC
--
-- * AST nodes
-- * Serialized size of DeBruijn version.
--
-- DeBruijn version is the one used in Script,
-- so names don't affect the serialized size.
--
statsUPLC :: HasUPLC a => a -> (Integer, Integer)
statsUPLC term = (UPLC.termSize t, UPLC.serialisedSize t)
  where
    t :: UPLC.Term UPLC.DeBruijn DefaultUni DefaultFun ()
    t = renameToDeBruijn (viewUPLC term)

-- | View 'UPLC.Term' inside @a@.
viewUPLC :: HasUPLC a => a -> UPLC.Term UPLC.NamedDeBruijn DefaultUni DefaultFun ()
viewUPLC = view uplc

-------------------------------------------------------------------------------
-- Pretty
-------------------------------------------------------------------------------

toDoc :: HasUPLC a => a -> PP.Doc ann
toDoc = (<> PP.line) . prettyClosedRaw . simplify . fromUPLC . viewUPLC

dumpWidth :: Int
dumpWidth = 250

putDocT :: Int -> PP.Doc ann -> Text
putDocT w doc = renderStrict sdoc where
    sdoc :: PP.SimpleDocStream ()
    sdoc = PP.layoutSmart layoutOptions (PP.unAnnotate doc)
    layoutOptions = PP.LayoutOptions { PP.layoutPageWidth = PP.AvailablePerLine w 1 }

putDocW :: Int -> PP.Doc ann -> IO ()
putDocW w doc = renderIO stdout sdoc where
    sdoc :: PP.SimpleDocStream ()
    sdoc = PP.layoutSmart layoutOptions (PP.unAnnotate doc)
    layoutOptions = PP.LayoutOptions { PP.layoutPageWidth = PP.AvailablePerLine w 1 }

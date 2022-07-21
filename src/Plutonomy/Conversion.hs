-- | Conversions between @plutus-core@ and @plutonomy@ terms.
module Plutonomy.Conversion (
    fromUPLC,
    toUPLC,
) where

import Control.Monad      (void)
import Data.Void          (Void)
import PlutusCore.Default (DefaultFun, DefaultUni)
import PlutusCore.Quote   (Quote, freshName, runQuote, runQuoteT)
import Subst              (Nat (Z), Var (..), instantiate1, absurdVar, vacuousFree)

import qualified UntypedPlutusCore as UPLC

import Plutonomy.Constant
import Plutonomy.Name
import Plutonomy.Raw
import Plutonomy.PlutusExtras

-------------------------------------------------------------------------------
-- From
-------------------------------------------------------------------------------

class FromUPLC name where
    -- | Convert closed 'UPLC.Term' to bound @'Term' a@.
    fromUPLC :: UPLC.Term name DefaultUni DefaultFun ann -> Raw a n

instance FromUPLC UPLC.Name where
    fromUPLC namedTerm =
        go (\name -> error $ "Unbound name " ++ show name) namedTerm
      where
        go :: (UPLC.Name -> Var n) -> UPLC.Term UPLC.Name DefaultUni DefaultFun ann -> Raw a n
        go  ctx (UPLC.Var _ann x)      = Var (ctx x)
        go  ctx (UPLC.Apply _ann f t)  = App (go ctx f) (go ctx t)
        go  ctx (UPLC.LamAbs _ann n t) = Lam (Name (UPLC.nameString n)) $
            go (\n' -> if n == n' then VZ else VS (ctx n')) t
        go  ctx (UPLC.Force _ann t)    = Force (go ctx t)
        go  ctx (UPLC.Delay _ann t)    = Delay (go ctx t)
        go _ctx (UPLC.Constant _ann c) = Constant (constantFromPlutus c)
        go _ctx (UPLC.Builtin _ann b)  = Builtin b
        go _ctx (UPLC.Error _ann)      = Error

instance FromUPLC UPLC.NamedDeBruijn where
    fromUPLC deBruijnTerm = fromUPLC namedTerm
      where
        -- We convert to unique names as these are easier to convert from
        namedTerm :: UPLC.Term UPLC.Name DefaultUni DefaultFun ()
        namedTerm = case runQuoteT $ UPLC.unDeBruijnTerm deBruijnTerm of
            Left e  -> error $ "Converting from deBruijn " ++ show (e :: UPLC.FreeVariableError)
            Right t -> void t

-------------------------------------------------------------------------------
-- To
-------------------------------------------------------------------------------

class ToUPLC name where
    -- | Convert closed bound 'Term' to 'UPLC.Term'.
    toUPLC :: Raw Void Z -> UPLC.Term name DefaultUni DefaultFun ()

instance ToUPLC UPLC.Name where
    toUPLC term = runQuote $ go $ vacuousFree term
      where
        go :: Raw UPLC.Name Z -> Quote (UPLC.Term UPLC.Name DefaultUni DefaultFun ())
        go (Var x)          = absurdVar x
        go (Free x)         = return (UPLC.Var ann x)
        go (Lam (Name n) t) = do
            name <- freshName n
            UPLC.LamAbs ann name <$> go (instantiate1 (Free name) t)
        go (App f t)        = UPLC.Apply ann <$> go f <*> go t
        go (Force t)        = UPLC.Force ann <$> go t
        go (Delay t)        = UPLC.Delay ann <$> go t
        go (Constant c)     = return (UPLC.Constant ann (constantToPlutus c))
        go (Builtin b)      = return (UPLC.Builtin ann b)
        go Error            = return (UPLC.Error ann)

        go (Let (Name n) t s) = do
            name <- freshName n
            mk name <$> go t <*> go (instantiate1 (Free name) s)
          where
            mk name t' s' = UPLC.Apply ann (UPLC.LamAbs ann name s') t'

        ann :: ()
        ann = ()

instance ToUPLC UPLC.NamedDeBruijn where
    toUPLC term = case UPLC.deBruijnTerm $ toUPLC term of
        Left exc    -> error $ "Converting to deBruijn " ++ show (exc :: UPLC.FreeVariableError)
        Right term' -> term'

instance ToUPLC UPLC.DeBruijn where
    toUPLC = renameUPLC (\(UPLC.NamedDeBruijn _ i) -> UPLC.DeBruijn i) . toUPLC

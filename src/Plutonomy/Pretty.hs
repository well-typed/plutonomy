{-# LANGUAGE OverloadedStrings #-}
module Plutonomy.Pretty (
    prettyClosedRaw,
    prettyRaw,
) where

import Control.Monad.Trans.State (State, evalState, state)
import Data.Char                 (isAscii, isPrint)
import Data.Maybe                (fromMaybe)
import Data.Text                 (Text)
import Data.Void                 (Void, absurd)
import PlutusCore.Data           (Data (..))
import PlutusCore.Default        (DefaultUni (..), Some (..), ValueOf (..))
import Prettyprinter             ((<+>))
import Subst                     (Nat (Z), instantiate1, free)

import qualified Data.Map.Strict    as Map
import qualified Data.Text          as T
import qualified Data.Text.Encoding as TE
import qualified Prettyprinter      as PP
import qualified Control.Lens as L

import Plutonomy.Name
import Plutonomy.Raw

-- | Pretty print closed term
--
-- See 'prettyRaw'.
prettyClosedRaw :: Raw Void Z -> PP.Doc ann
prettyClosedRaw = prettyRaw absurd

-- | 'prettyRaw' pretty-prints the 'Term' in more Haskell-like syntax.
--
-- * Variables are printed as is
--
-- * Lambda abstraction is printed as @\\ name -> body@. Nested abstractions
--   are combined into @\\ name1 name2 ... nameN -> body@.
--
-- * Function application is simply a juxtaposition
--
-- * Delayed and forced terms are @\\ ~ -> term@ and @body !@ respectively.
--
-- * Constants, builtins are suffixed with @#@.
--
-- * Error is printed as @ERROR@.
--
-- * Let bindings (present in @plutonomy@ term representation) are printed as:
--
--   @
--   let* global1 = def1
--        global2 = def2
--   in term
--   @
--
prettyRaw :: forall a n ann. (a -> PP.Doc ann) -> Raw a n -> PP.Doc ann
prettyRaw ctx term = evalState (go 0 (L.over free ctx term)) Map.empty where
    go :: forall m. Int -> Raw (PP.Doc ann) m -> Names (PP.Doc ann)
    go _ (Var x)    = pure ("$" <> PP.pretty (show x))
    go _ (Free x)   = pure x

    go d t@(App {})   = parens (d > 10) $ ppApp g xs where (g, xs) = peelApp t
    go d t@(Force {}) = parens (d > 10) $ ppApp g xs where (g, xs) = peelApp t
    go d t@(Lam {})   = do
        (names, t') <- peelLam t
        parens (d > 0) $ ppLam names t'
    go d t@(Delay {}) = do
        (names, t') <- peelLam t
        parens (d > 0) $ ppLam names t'
    go d t@(Let {})   = do
        (defs, t') <- peelLet t
        parens (d > 0) $ ppLet defs t'

    -- We slightly change how constants are printed:
    go _d (Constant (Some (ValueOf DefaultUniData d))) =
        pure (prettyData d <> "#d")
    go _d (Constant (Some (ValueOf DefaultUniString t))) =
        pure (PP.viaShow t <> "#t")
    go _d (Constant c@(Some (ValueOf DefaultUniByteString bs))) =
        pure $ case TE.decodeUtf8' bs of
            Right t | T.all isAsciiPrint t -> PP.viaShow t <> "#b"
            _                              -> PP.pretty c <> "#b"

    go _d (Constant c)  = pure (PP.pretty c <> "#")
    go _d (Builtin b)   = pure (PP.pretty b <> "#")
    go _d Error         = pure "ERROR"

    parens True doc  = PP.parens <$> doc
    parens False doc = doc

    ppLam :: [Abs ann] -> Raw (PP.Doc ann) m -> Names (PP.Doc ann)
    ppLam names t = mk <$> go 0 t where
        mk t' = PP.hang indentw $ PP.sep
            [ "\\" <+> PP.hsep (map goAbs names) <+> "->"
            , t'
            ]

        goAbs (AbsName n) = n
        goAbs AbsDelay    = "~"

    ppApp :: Raw (PP.Doc ann) m -> [Arg (PP.Doc ann) m] -> Names (PP.Doc ann)
    ppApp f xs = mk <$> go 11 f <*> traverse goArg xs where
        mk f' []                           = f'
        mk f' (Nothing : xs') | isSimple f = mk (f' <+> "!") xs'
        mk f' xs'                          = PP.hang indentw $ PP.sep $ f' : map (fromMaybe "!") xs'

        goArg (ArgTerm t) = Just <$> go 11 t
        goArg ArgForce    = pure Nothing

        isSimple (Var _)     = True
        isSimple (Builtin _) = True
        isSimple _           = False

    ppLet :: [(PP.Doc ann, PP.Doc ann)] -> Raw (PP.Doc ann) m -> Names (PP.Doc ann)
    ppLet defs t = mk defs <$> go 0 t
      where
        mk defs' t' = PP.align $ PP.vsep
            [ "let*" <+> PP.align (hardvsep
                [ PP.hang indentw $ PP.sep
                    [ n <+> "="
                    , d
                    ]
                | (n, d) <- defs'
                ])

            , "in" <+> t'
            ]

    hardvsep []     = mempty
    hardvsep (x:xs) = x <> foldMap (PP.flatAlt PP.hardline "; " <>) xs

    peelLet
        :: Raw (PP.Doc ann) m
        -> Names ([(PP.Doc ann, PP.Doc ann)], Raw (PP.Doc ann) m)
    peelLet (Let (Name n) t s) = do
        n' <- newName n
        t' <- go 0 t
        res <- peelLet $ instantiate1 (Free n') s
        case res of ~(defs, s') -> pure ((n', t') : defs, s')
      where
    peelLet t =
        pure ([], t)

prettyData :: Data -> PP.Doc ann
prettyData = go where
    go (Constr i ds) = PP.angles (PP.sep (PP.pretty i : PP.punctuate PP.comma (fmap go ds)))
    go (Map entries) = PP.braces (PP.sep (PP.punctuate PP.comma (fmap (\(k, v) -> go k <> ":" <+> go v) entries)))
    go (List ds)     = PP.brackets (PP.sep (PP.punctuate PP.comma (fmap go ds)))
    go (I i)         = PP.pretty i
    go (B b)         = PP.viaShow b

isAsciiPrint :: Char -> Bool
isAsciiPrint c = isAscii c && isPrint c

-------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------

type Names = State (Map.Map Text Int)

indentw :: Int
indentw = 2

newName :: Text -> Names (PP.Doc ann)
newName t = state $ \s -> case Map.lookup t s of
    Nothing -> (PP.pretty t, Map.insert t 0 s)
    Just i  -> (PP.pretty t <> "_" <> PP.pretty (str i []), Map.insert t (i + 1) s)
  where
    chars = "0123456789abcdefghijkmnprstuvwxyz"
    str i = case i `divMod` length chars of
        (0, n) -> ((chars !! n) :)
        (m, n) -> str m . ((chars !! n) :)

peelLam :: Raw (PP.Doc ann) n -> Names ([Abs ann], Raw (PP.Doc ann) n)
peelLam (Lam (Name n) t) = do
    n' <- newName n
    res <- peelLam $ instantiate1 (Free n') t
    case res of ~(names, t') -> pure (AbsName n' : names, t')
peelLam (Delay t) = do
    res <- peelLam t
    case res of ~(names, t') -> pure (AbsDelay : names, t')
peelLam t =
    pure ([], t)

data Abs ann
    = AbsName (PP.Doc ann)
    | AbsDelay

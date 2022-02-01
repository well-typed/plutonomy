-- | Names.
module Plutonomy.Name where

import Data.String (IsString (..))
import Data.Text   (Text)

import qualified Data.Text     as T
import qualified Prettyprinter as PP

import Plutonomy.Orphans ()

-- | 'Name'. Note these names are irrelevant: they are all equal.
-- We carry them for humans, machine doesn't care.
newtype Name = Name Text

instance Show Name where
    showsPrec d (Name t) = showsPrec d t

instance IsString Name where
    fromString = Name . fromString

instance Semigroup Name where
    Name x <> Name y = Name (x <> y)

instance PP.Pretty Name where
    pretty (Name n) = PP.pretty n

instance Eq Name where
    _ == _ = True

instance Ord Name where
    compare _ _ = EQ

-- | Derive a forced 'Name'
--
-- >>> forcedName "foo"
-- "foo!"
--
-- >>> forcedName "~bar"
-- "bar"
--
forcedName :: Name -> Name
forcedName (Name t) = case T.uncons t of
    Just ('~', t') -> Name t'
    _              -> Name $ T.snoc t '!'

unusedName :: Name -> Name
unusedName = id -- TODO

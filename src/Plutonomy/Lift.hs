module Plutonomy.Lift where

import Data.ByteString    (ByteString)
import Data.Text          (Text)
import PlutusCore.Data    (Data)
import PlutusCore.Default (DefaultUni (..), Esc, Some (..), ValueOf (..))
import PlutusTx.IsData    (ToData (..), toData)

import Plutonomy.Raw

-- $setup
-- >>> import Plutonomy
-- >>> import PlutusCore.Data (Data (..))
-- >>> import qualified Data.ByteString as BS
-- >>> import qualified Data.Text as T

-- | Class for lifting (constant) values into terms.
class Lift a where
    defaultUni :: DefaultUni (Esc a)

-- | Lift value into a 'Raw'.
lift :: Lift a => a -> Raw n b
lift x = Constant (Some (ValueOf defaultUni x))

-- | Lift a 'Data' representation of a value to 'Raw'.
liftData :: ToData a => a -> Raw n b
liftData x = lift (toData x)

-- |
--
-- >>> prettyClosedRaw $ lift ()
-- ()#
--
instance Lift () where
    defaultUni = DefaultUniUnit

-- |
--
-- >>> prettyClosedRaw $ lift (42 :: Integer)
-- 42#
instance Lift Bool where
    defaultUni = DefaultUniBool

instance Lift Integer where
    defaultUni = DefaultUniInteger

-- |
--
-- >>> prettyClosedRaw $ lift $ BS.empty
-- ""#b
--
-- >>> prettyClosedRaw $ lift ("secret" :: BS.ByteString)
-- "secret"#b
--
-- >>> prettyClosedRaw $ lift $ BS.pack [0,1,2]
-- #000102#b
--
instance Lift ByteString where
    defaultUni = DefaultUniByteString

-- |
--
-- >>> prettyClosedRaw $ lift ("secret" :: T.Text)
-- "secret"#t
--
instance Lift Text where
    defaultUni = DefaultUniString

instance Lift a => Lift [a] where
    defaultUni = DefaultUniApply DefaultUniProtoList defaultUni

-- |
--
-- >>> prettyClosedRaw $ lift $ Constr 0 []
-- <0>#d
instance Lift Data where
    defaultUni = DefaultUniData

-- | Information about builtins.
module Plutonomy.Builtins where

import PlutusCore.Default (DefaultFun(..))

import Plutonomy.Orphans ()

-- | Arity of builtin functions ('DefaultFun').
-- Note that arity includes forcing arguments too.
--
-- When builtin is not fully saturated it can be considered a value.
--
builtinArity :: DefaultFun -> Int
-- Type signatures given by `plc print-builtin-signatures`
builtinArity Trace                    = 3  -- [ forall a, string, a ] -> a
builtinArity AddInteger               = 2  -- [ integer, integer ] -> integer
builtinArity SubtractInteger          = 2  -- [ integer, integer ] -> integer
builtinArity MultiplyInteger          = 2  -- [ integer, integer ] -> integer
builtinArity DivideInteger            = 2  -- [ integer, integer ] -> integer
builtinArity QuotientInteger          = 2  -- [ integer, integer ] -> integer
builtinArity RemainderInteger         = 2  -- [ integer, integer ] -> integer
builtinArity ModInteger               = 2  -- [ integer, integer ] -> integer
builtinArity EqualsInteger            = 2  -- [ integer, integer ] -> bool
builtinArity LessThanInteger          = 2  -- [ integer, integer ] -> bool
builtinArity LessThanEqualsInteger    = 2  -- [ integer, integer ] -> bool
builtinArity AppendByteString         = 2  -- [ bytestring, bytestring ] -> bytestring
builtinArity ConsByteString           = 2  -- [ integer, bytestring ] -> bytestring
builtinArity SliceByteString          = 3  -- [ integer, integer, bytestring ] -> bytestring
builtinArity LengthOfByteString       = 1  -- [ bytestring ] -> integer
builtinArity IndexByteString          = 2  -- [ bytestring, integer ] -> integer
builtinArity EqualsByteString         = 2  -- [ bytestring, bytestring ] -> bool
builtinArity LessThanByteString       = 2  -- [ bytestring, bytestring ] -> bool
builtinArity LessThanEqualsByteString = 2  -- [ bytestring, bytestring ] -> bool
builtinArity Sha2_256                 = 1  -- [ bytestring ] -> bytestring
builtinArity Sha3_256                 = 1  -- [ bytestring ] -> bytestring
builtinArity Blake2b_256              = 1  -- [ bytestring ] -> bytestring
builtinArity VerifySignature          = 3  -- [ bytestring, bytestring, bytestring ] -> bool
builtinArity AppendString             = 2  -- [ string, string ] -> string
builtinArity EqualsString             = 2  -- [ string, string ] -> bool
builtinArity EncodeUtf8               = 1  -- [ string ] -> bytestring
builtinArity DecodeUtf8               = 1  -- [ bytestring ] -> string
builtinArity IfThenElse               = 4  -- [ forall a, bool, a, a ] -> a
builtinArity ChooseUnit               = 3  -- [ forall a, unit, a ] -> a
builtinArity FstPair                  = 3  -- [ forall a, forall b, pair(a, b) ] -> a
builtinArity SndPair                  = 3  -- [ forall a, forall b, pair(a, b) ] -> b
builtinArity ChooseList               = 5  -- [ forall a, forall b, list(a), b, b ] -> b
builtinArity MkCons                   = 3  -- [ forall a, a, list(a) ] -> list(a)
builtinArity HeadList                 = 2  -- [ forall a, list(a) ] -> a
builtinArity TailList                 = 2  -- [ forall a, list(a) ] -> list(a)
builtinArity NullList                 = 2  -- [ forall a, list(a) ] -> bool
builtinArity ChooseData               = 7  -- [ forall a, data, a, a, a, a, a ] -> a
builtinArity ConstrData               = 2  -- [ integer, list(data) ] -> data
builtinArity MapData                  = 1  -- [ list(pair(data, data)) ] -> data
builtinArity ListData                 = 1  -- [ list(data) ] -> data
builtinArity IData                    = 1  -- [ integer ] -> data
builtinArity BData                    = 1  -- [ bytestring ] -> data
builtinArity UnConstrData             = 1  -- [ data ] -> pair(integer, list(data))
builtinArity UnMapData                = 1  -- [ data ] -> list(pair(data, data))
builtinArity UnListData               = 1  -- [ data ] -> list(data)
builtinArity UnIData                  = 1  -- [ data ] -> integer
builtinArity UnBData                  = 1  -- [ data ] -> bytestring
builtinArity EqualsData               = 2  -- [ data, data ] -> bool
builtinArity MkPairData               = 2  -- [ data, data ] -> pair(data, data)
builtinArity MkNilData                = 1  -- [ unit ] -> list(data)
builtinArity MkNilPairData            = 1  -- [ unit ] -> list(pair(data, data))

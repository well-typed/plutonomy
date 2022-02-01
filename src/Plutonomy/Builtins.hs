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
builtinArity Trace                    = 3
builtinArity AddInteger               = 2
builtinArity SubtractInteger          = 2
builtinArity MultiplyInteger          = 2
builtinArity DivideInteger            = 2
builtinArity QuotientInteger          = 2
builtinArity RemainderInteger         = 2
builtinArity ModInteger               = 2
builtinArity EqualsInteger            = 2
builtinArity LessThanInteger          = 2
builtinArity LessThanEqualsInteger    = 2
builtinArity AppendByteString         = 2
builtinArity ConsByteString           = 2
builtinArity SliceByteString          = 3
builtinArity LengthOfByteString       = 1
builtinArity IndexByteString          = 2
builtinArity EqualsByteString         = 2
builtinArity LessThanByteString       = 2
builtinArity LessThanEqualsByteString = 2
builtinArity Sha2_256                 = 1
builtinArity Sha3_256                 = 1
builtinArity Blake2b_256              = 1
builtinArity VerifySignature          = 2
builtinArity AppendString             = 2
builtinArity EqualsString             = 2
builtinArity EncodeUtf8               = 1
builtinArity DecodeUtf8               = 1
builtinArity IfThenElse               = 4  -- \@a p t e -> if p then t else e
builtinArity ChooseUnit               = 1
builtinArity FstPair                  = 3  -- \@a @b p -> fst p
builtinArity SndPair                  = 3  -- \@a @b p -> snd p
-- Conservative arity of 1:
builtinArity ChooseList               = 1  -- \@a @r xs n c -> case xs of { [] -> n; _:_ -> c }
builtinArity MkCons                   = 1
builtinArity HeadList                 = 2  -- \@a xs -> head xs
builtinArity TailList                 = 2  -- \@a xs -> tail xs
builtinArity NullList                 = 2 --- \@a xs -> null xs
builtinArity ChooseData               = 1
builtinArity ConstrData               = 2  -- \i args -> Constr i args
builtinArity MapData                  = 1
builtinArity ListData                 = 1
builtinArity IData                    = 1
builtinArity BData                    = 1
builtinArity UnConstrData             = 1  -- \d -> case d of ...
builtinArity UnMapData                = 1  -- \d -> case d of ...
builtinArity UnListData               = 1  -- \d -> case d of ...
builtinArity UnIData                  = 1  -- \d -> case d of ...
builtinArity UnBData                  = 1  -- \d -> case d of ...
builtinArity EqualsData               = 2  -- \x y -> x == y
builtinArity MkPairData               = 1
builtinArity MkNilData                = 1
builtinArity MkNilPairData            = 1

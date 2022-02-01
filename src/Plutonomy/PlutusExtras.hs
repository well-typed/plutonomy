{-# LANGUAGE OverloadedStrings #-}
-- | Module with extras for @plutus-core@.
module Plutonomy.PlutusExtras where

import qualified UntypedPlutusCore as UPLC

import Plutonomy.Orphans ()

renameUPLC :: (name -> name') -> UPLC.Term name uni fun ann -> UPLC.Term name' uni fun ann
renameUPLC rnm = go where
    go (UPLC.Var ann n       ) = UPLC.Var ann (rnm n)
    go (UPLC.LamAbs ann n t  ) = UPLC.LamAbs ann (rnm n) (go t)
    go (UPLC.Apply ann t1 t2 ) = UPLC.Apply ann (go t1) (go t2)
    go (UPLC.Delay ann t     ) = UPLC.Delay ann (go t)
    go (UPLC.Force ann t     ) = UPLC.Force ann (go t)
    go (UPLC.Constant ann con) = UPLC.Constant ann con
    go (UPLC.Builtin ann bn  ) = UPLC.Builtin ann bn
    go (UPLC.Error ann       ) = UPLC.Error ann

renameToDeBruijn :: UPLC.Term UPLC.NamedDeBruijn uni fun ann -> UPLC.Term UPLC.DeBruijn uni fun ann
renameToDeBruijn = renameUPLC (\(UPLC.NamedDeBruijn _ i) -> UPLC.DeBruijn i)

renameFromDeBruijn :: UPLC.Term UPLC.DeBruijn uni fun ann -> UPLC.Term UPLC.NamedDeBruijn uni fun ann
renameFromDeBruijn = renameUPLC (\(UPLC.DeBruijn i) -> UPLC.NamedDeBruijn "x" i)

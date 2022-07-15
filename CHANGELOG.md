0.20220715
----------

* Correct `builtinArity`
* Special treatment of `fix`:
  `let go = fix (\rec x -> ...) in go ...` functions should be inlined now.
* Support `plutus` version used by `cardano-node-1.35.1`

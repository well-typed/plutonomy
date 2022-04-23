0.2022mmdd
----------

* Correct `builtinArity`
* Special treatment of `fix`:
  `let go = fix (\rec x -> ...) in go ...` functions should be inlined now.

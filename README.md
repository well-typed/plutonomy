# plutonomy

plutonomy is an optimizer for untyped plutus core.

It can be plugged into any Plutus compilation pipeline, by
adding an extra pass. The optimiser is configurable to an
extent. At the default optimisation level, the optimiser should
exactly preserve the semantics of the original code. At a
particularly aggressive optimisation level, the optimiser can
perform certain transformations that may not preserve the
semantics.

The main optimiser entry point is `Plutonomy.UPLC.optimizeUPLC` or
`Plutonomy.UPLC.optimizeUPLCWith` if you want to deviate from the default
configuration options.

The library additionally provides its own variants of
validator scripts and minting policy scripts
(via `Plutonomy.Scripts.mkValidatorScript` and
`Plutonomy.Scripts.mkMintingPolicyScript`) that can
be turned back into their Plutus counterparts via
`Plutonomy.Scripts.validatorToPlutus` and
`Plutonomy.Scripts.mintingPolicyToPlutus`. The Plutonomy
representation is intended for debugging / inspection
as it uses names for binders instead of de Bruijn indices.

More extensive documentation of the library is forthcoming.

Any use of the library as well as feedback is welcome, but due
to timing constraints, we cannot current guarantee any level
of unpaid support.

## Flags

plutonomy currently supports two plutus versions,
identified via their git commit hashes.
You need to toggle one of the flags:

- plutus-1efbb276e
- plutus-4710dff2e

For example, add to your `cabal.project`:

```
flags: +plutus-1efbb276e
```

None of the two flags are on by default,
so you need to enable the flag corresponding to
the version you want to use, but never turn off
any version flags.

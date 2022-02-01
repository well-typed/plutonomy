# plutonomy

plutonomy is an optimizer for untyped plutus core.

## Flags

plutonomy supports few plutus versions,
you need to toggle one of the flags:

- plutus-1efbb276e
- plutus-4710dff2e

For example, add to your `cabal.project`:

```
flags: +plutus-1efbb276e
```

None of flags is on by default,
so you don't need to turn off any flags.

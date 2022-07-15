#!/bin/sh

# haskell-ci regenerate won't regenerate all CI jobs.
# therefore we have a script for that

haskell-ci github --config cabal.1efbb276e.haskell-ci --project cabal.1efbb276e.project -o .github/workflows/haskell-ci.1efbb276e.yml
haskell-ci github --config cabal.4710dff2e.haskell-ci --project cabal.4710dff2e.project -o .github/workflows/haskell-ci.4710dff2e.yml
haskell-ci github --config cabal.f680ac697.haskell-ci --project cabal.f680ac697.project -o .github/workflows/haskell-ci.f680ac697.yml

# Changelog for `sequitur`

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to the
[Haskell Package Versioning Policy](https://pvp.haskell.org/).

## Unreleased

* add `decodeNonTerminalsToMonoid` function
* rename `RuleId` type to `NonTerminalSymbol`
* add a benchmark program `sequitur-bench` (Thanks to [MangoIV](https://github.com/MangoIV))
* change `Grammar` type from a type synonym to a `newtype`, and add instances of `Foldable`, `IsList`, and `IsString`
* introduce `IsTerminalSymbol` class synonym for absorbing the difference between `hashable` `<1.4.0.0` and `>=1.4.0.0`.
* use `ST` monad internally instead of arbitrary `PrimMonad` to allow GHC to inline `(>>=)` to produce more efficient code
* add `sequitur-demo` program
* add some sanity checks which are disabled by default

## 0.1.0.0 - 2024-07-13

* initial release

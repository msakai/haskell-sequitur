# Haskell implementation of _SEQUITUR_ algorithm

[![build](https://github.com/msakai/haskell-sequitur/actions/workflows/build.yaml/badge.svg)](https://github.com/msakai/haskell-sequitur/actions/workflows/build.yaml)

## About _SEQUITUR_

_SEQUITUR_ is a linear-time, online algorithm for producing a context-free
grammar from an input sequence. The resulting grammar is a compact representation
of original sequence and can be used for data compression.

Example:

- Input string: `abcabcabcabcabc`

- Resulting grammar
  - `S` → `AAB`
  - `A` → `BB`
  - `B` → `abc`

_SEQUITUR_ consumes input symbols one-by-one and append each symbol at the end of the
grammar's start production (`S` in the above example), then substitutes repeating
patterns in the given sequence with new rules. _SEQUITUR_ maintains two invariants:

* **Digram Uniqueness**: _SEQUITUR_ ensures that no digram
  (a.k.a. bigram) occurs more than once in the grammar. If a digram
  (e.g. `ab`) occurs twice, SEQUITUR introduce a fresh non-terminal
  symbol (e.g. `M`) and a rule (e.g. `M` → `ab`) and replace
  original occurences with the newly introduced non-terminals.  One
  exception is the cases where two occurrence overlap.

* **Rule Utility**: If a non-terminal symbol occurs only once,
  _SEQUITUR_ removes the associated rule and substitute the occurence
  with the right-hand side of the rule.

## Usage

```console
ghci> import Language.Grammar.Sequitur
ghci> encode "baaabacaa"
fromList [(0,[NonTerminal 1,NonTerminal 2,NonTerminal 1,Terminal 'c',NonTerminal 2]),(1,[Terminal 'b',Terminal 'a']),(2,[Terminal 'a',Terminal 'a'])]
```

The output represents the following grammar:

```
0 → 1 2 1 c 2
1 → b a
2 → a a
```


## References

- [Sequitur algorithm - Wikipedia](https://en.m.wikipedia.org/wiki/Sequitur_algorithm)
- [sequitur.info](http://www.sequitur.info/)
- Nevill-Manning, C.G. and Witten, I.H. (1997) "[Identifying
  Hierarchical Structure in Sequences: A linear-time
  algorithm](https://doi.org/10.1613/jair.374)," Journal of
  Artificial Intelligence Research, 7, 67-82.

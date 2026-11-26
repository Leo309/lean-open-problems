# lean-open-problems

Results on open problems and conjectures, each with a proof checked by the
Lean 4 kernel. One directory per result. Only finished and verified results
are kept here.

| Directory | Result | Status |
| --- | --- | --- |
| [`a215926/`](a215926/) | The first conjecture in OEIS A215926 is equivalent to the conjecture that every almost perfect number is a power of 2; the second conjecture follows from it | Lean-verified. Numerical search to 10^16 not formalized |
| [`a017666/`](a017666/) | Coleman's conjecture in OEIS A017666 (if the denominator of σ(n)/n is practical, then n is practical) is equivalent to the nonexistence of odd multiply perfect numbers | Lean-verified |

## Checking the proofs

All results share one Lean project, pinned to Lean 4.36.0 and Mathlib v4.36.0.

```
lake exe cache get   # optional, downloads prebuilt Mathlib
lake build           # builds every result
lake build A215926   # builds one result
lake build A017666
```

A result is accepted here only if its file builds with no `sorry` and its main
theorems depend on no axioms beyond `propext`, `Classical.choice` and
`Quot.sound`. Each result's README lists the main theorems and says exactly
which claims are formalized and which are not.

Each finished result gets a git tag (for example `a215926-v1`), so that a paper
can cite a fixed version.

## Use of AI

The proofs, the Lean formalizations and the programs in this repository were
produced by Claude, an AI system developed by Anthropic, at the request of the
repository owner. Correctness of the formalized theorems rests on the Lean
kernel, not on the AI system. Statements of conjectures are taken from their
original sources, which are cited in each directory.

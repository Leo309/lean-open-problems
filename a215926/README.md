# OEIS A215926 and almost perfect numbers

Lean 4 proof, search program and manuscript for the following result.

For `n ≥ 2` let `a(n)` be the smallest deficient number `k` such that `k·n` is
not deficient ([OEIS A215926](https://oeis.org/A215926)). The OEIS entry states
two conjectures (M. Marcus, 2012):

1. `a(n)` is always `1`, `3`, or a power of `2`.
2. For `m ≥ 1`, the first `n ≥ 2` with `a(n) = 2^m` is the least prime greater
   than `2^m`.

A number `k` is *almost perfect* if `σ(k) = 2k − 1`. Every power of 2 is almost
perfect; whether there are others is a classical open problem.

**Results.**

- Conjecture 1 is *equivalent* to the statement that every almost perfect number
  is a power of 2.
- Conjecture 2 follows from that statement. The converse is not known.
- Unconditionally: `a(n) ∈ {1, 2, 3}` for even `n`; for odd `n`, `a(n) ≤ n` and
  `a(n)` is a power of 2 or an almost perfect number that is not a power of 2.
- If no almost perfect number other than powers of 2 is `≤ N`, then Conjecture 1
  holds for all `n ≤ N` and Conjecture 2 for all `m` with `2^m ≤ N + 1`.

So neither conjecture is settled here: Conjecture 1 is shown to be exactly as
hard as a known open problem. The proofs are short and elementary.

## Files

| File | Content |
| --- | --- |
| `A215926.lean` | Lean 4 formalization of all the results above (about 800 lines) |
| `almost_perfect_search.c` | Search for almost perfect numbers up to `10^16` |
| `paper/a215926.tex`, `paper/a215926.pdf` | Manuscript by Hao Li, with human-readable proofs |

## Checking the proof

From the repository root:

```
lake exe cache get   # optional, downloads prebuilt Mathlib
lake build A215926
```

Verified with Lean 4.36.0 and Mathlib v4.36.0, as pinned in the repository root.

The build succeeds with no `sorry`. The definitions of `a`, `nextPrimeTwoPow`
and `AlmostPerfect` and the statements of the two conjectures are copied from
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/OEIS/215926.lean` and
`FormalConjectures/Wikipedia/AlmostPerfectNumbers.lean`). Main theorems:

| Lean theorem | Statement |
| --- | --- |
| `conjecture_1_iff_almostPerfect` | Conjecture 1 ⟺ no almost perfect number other than powers of 2 |
| `conjectures_of_no_exotic_almostPerfect` | that statement implies Conjectures 1 and 2 |
| `a_even`, `a_odd`, `a_le_self` | unconditional structure of `a(n)` |
| `exists_a_eq_of_exotic` | the least exotic almost perfect number `k` is a value `a(n)` |
| `nextPrime_le_of_a_eq`, `a_nextPrime` | the two halves of Conjecture 2 |
| `conjecture_1_of_bound`, `conjecture_2_of_bound` | bounded versions |
| `conjecture_1_small`, `conjecture_2_small` | `n < 256` and `m ≤ 8`, unconditionally. A consistency check only: the OEIS table to `n = 10000` already covers more |

Every theorem depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound` (check with `#print axioms`).

## The search

```
cc -O2 -o ap almost_perfect_search.c
./ap 100000000
```

Output: `M=100000000 L=M^2 tested=170710624 found=0`. It tests every
`k = 2^a·b^2 ≤ 10^16` with `b ≥ 3` odd. This computation is **not** formally
verified. It gives Conjecture 1 for `n ≤ 10^16` and Conjecture 2 for `m ≤ 53`.

## Use of AI

The results, the proofs, the Lean formalization, the search program and the
first draft of the manuscript were produced by Claude, an AI system developed by
Anthropic, at the author's request. Correctness of the theorems rests on the
Lean kernel, not on the AI system.

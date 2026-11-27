# OEIS A050972: Coleman's conjecture on friendly pairs and practical numbers is false

Lean 4 proof of the following result.

Two positive integers `a < b` are a *friendly pair* if they have the same
abundancy index, `σ(a)/a = σ(b)/b`. [OEIS A050972](https://oeis.org/A050972)
lists the smaller members and [A050973](https://oeis.org/A050973) the larger
members of all friendly pairs. A positive integer `n` is *practical*
([OEIS A005153](https://oeis.org/A005153)) if every `m ≤ n` is a sum of
distinct divisors of `n`. The entry A050972 states (J. Coleman, 2014):

> Conjecture: if `a(n)` is in A005153, then `A050973(n)` is in A005153.

That is: if the smaller member of a friendly pair is practical, so is the
larger member.

**Results.**

- The conjecture is false. `(42, 544635)` is a friendly pair with common
  abundancy `16/7`; `42` is practical and `544635 = 3^2·5·7^2·13·19` is odd,
  hence not practical.
- There are infinitely many counterexamples: `(42·11^j, 544635·11^j)` for
  every `j ≥ 0`.
- Parity is not the only obstruction: `(13479018, 21180250)` is a friendly
  pair of even numbers with common abundancy `2304/931`, where
  `13479018 = 2·3·7^2·19^2·127` is practical and `21180250 = 2·5^3·7^3·13·19`
  is not (the prime `5` exceeds `1 + σ(2) = 4`).

The pair `(42, 544635)` is a well-known example of a friendly pair of opposite
parity. What is recorded here is that it refutes the conjecture.

This is the companion of the conjecture at A017666 (see
[`../a017666/`](../a017666/)), which Coleman stated on the same day and which
turns out to be equivalent to the nonexistence of odd multiply perfect numbers.

## Files

| File | Content |
| --- | --- |
| `A050972.lean` | Lean 4 formalization (about 250 lines). Imports `A017666` for the definition of practical numbers and Stewart's criterion |
| `friendly_search.py` | Search program for counterexamples (not part of the verified statement) |

## Checking the proof

From the repository root:

```
lake build A050972
```

Verified with Lean 4.36.0 and Mathlib v4.36.0. The build succeeds with no
`sorry`. Main theorems:

| Lean theorem | Statement |
| --- | --- |
| `not_colemanFriendlyConjecture` | the conjecture, stated for all friendly pairs `a < b`, is false |
| `counterexample_42_544635` | `(42, 544635)` is friendly, `42` is practical, `544635` is not |
| `infinitely_many_counterexamples` | the same for `(42·11^j, 544635·11^j)`, every `j` |
| `even_counterexample` | `(13479018, 21180250)`: both even, friendly, first practical, second not |

Each of them depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## What is not claimed

- Minimality is not formalized. The search program finds that `(42, 544635)`
  is the counterexample with the smallest larger member, that it is the only
  one with larger member below `3·10^6`, and that there are 13 with larger
  member below `3·10^7`.
- The conjecture is formalized as a statement about all friendly pairs
  `a < b`, which is what the two sequences enumerate. The ordering of the
  sequences plays no role.
- Novelty: the OEIS entries A050972 and A050973 (snapshot of 2026-11-26) and a
  web search on 2026-11-27 show no refutation. MathSciNet, zbMATH and full
  texts of papers were not checked.

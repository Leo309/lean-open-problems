# OEIS A017666, practical numbers and odd multiply perfect numbers

Lean 4 proof of the following result.

Let `a(n)` be the denominator of `σ(n)/n` in lowest terms, that is
`a(n) = n / gcd(n, σ(n))` ([OEIS A017666](https://oeis.org/A017666)). A positive
integer `n` is *practical* ([OEIS A005153](https://oeis.org/A005153)) if every
`m ≤ n` is a sum of distinct divisors of `n`. The OEIS entry A017666 states
(J. Coleman, 2014):

> Conjecture: if `a(n)` is practical, then `n` is practical.

A number `N` is *multiply perfect* if `N ∣ σ(N)`. Whether an odd multiply
perfect number `N > 1` exists is a classical open problem; the case
`σ(N) = 2N` is the odd perfect number problem.

**Results.**

- Coleman's conjecture is *equivalent* to the statement that no odd multiply
  perfect number `N > 1` exists.
- Any counterexample `n` to the conjecture has a unitary divisor `N > 1`
  (so `gcd(N, n/N) = 1`) that is an odd multiply perfect number.
- For every bound `X`: the conjecture holds for all `n ≤ X` if and only if
  there is no odd multiply perfect number `N` with `1 < N ≤ X`.
- The special case mentioned in the OEIS comment (if `a(n)` is a power of 2,
  then `n` is practical) is equivalent to the same statement.
- Coleman's conjecture at [OEIS A007691](https://oeis.org/A007691) (2013),
  that every multiply perfect number is practical, is also equivalent to the
  same statement. So the conjectures at A017666 and at A007691 are equivalent
  to each other.

So the conjecture is not settled here: it is shown to be exactly as hard as a
known open problem. One direction was already noted in the OEIS comment (an odd
`n` with `a(n)` practical must be multiply perfect). The new part is the
converse: a counterexample of any kind, even or odd, produces an odd multiply
perfect number.

## Idea of the proof

Stewart's criterion: write `n = p_1^{e_1} ⋯ p_k^{e_k}` with `p_1 < ⋯ < p_k`.
Then `n` is practical if and only if every `p_i` is at most
`1 + σ(p_1^{e_1} ⋯ p_{i-1}^{e_{i-1}})`.

Suppose `a(n)` is practical and `n` is not. Take a prime `p` of `n` that
violates the criterion, and split `n = m·N`, where `m` collects the primes
below `p` and `N` the primes from `p` on. Because `a(n)` divides `n` and is
practical, the criterion applied to `a(n)` shows that `a(n)` has no prime
factor `≥ p`. Hence `N` divides `gcd(n, σ(n))`, so `N ∣ σ(n) = σ(m)·σ(N)`.
Every prime factor of `N` is larger than `σ(m) + 1`, so `N` is coprime to
`σ(m)` and odd, and therefore `N ∣ σ(N)`.

Conversely an odd multiply perfect `N > 1` has `a(N) = 1`, which is practical,
while `N` is not practical because `2` is not a sum of distinct odd divisors.

## Files

| File | Content |
| --- | --- |
| `A017666.lean` | Lean 4 formalization of all the results above (about 470 lines) |

## Checking the proof

From the repository root:

```
lake exe cache get   # optional, downloads prebuilt Mathlib
lake build A017666
```

Verified with Lean 4.36.0 and Mathlib v4.36.0, as pinned in the repository root.

The build succeeds with no `sorry`. The definitions of `a`, of practical numbers
and of membership in A005153 agree with those in
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjectures/OEIS/17666.lean`, `FormalConjectures/OEIS/5153.lean`,
`FormalConjecturesForMathlib/NumberTheory/PracticalNumbers.lean`), with the
definition of subset sums written out. Main theorems:

| Lean theorem | Statement |
| --- | --- |
| `coleman_iff_noOddMultiperfect` | Coleman's conjecture ⟺ no odd `N > 1` with `N ∣ σ(N)` |
| `counterexample_structure` | a counterexample has an odd multiply perfect unitary divisor `N > 1` |
| `coleman_bounded` | the same equivalence restricted to numbers `≤ X` |
| `coleman_dyadic_iff_noOddMultiperfect` | the power-of-2 special case is equivalent to the same statement |
| `multiperfectPractical_iff_noOddMultiperfect` | every multiply perfect number is practical ⟺ no odd `N > 1` with `N ∣ σ(N)` |
| `SC_of_stewart` | sufficiency half of Stewart's criterion for practical numbers |
| `practical_prime_le` | necessity half, in the form used here |

Each of them depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## What is not claimed

- Neither Coleman's conjecture nor the nonexistence of odd multiply perfect
  numbers is proved.
- Lower bounds for odd multiply perfect numbers from the literature are not
  formalized here. Through `coleman_bounded`, any such bound `X` gives the
  conjecture for all `n ≤ X`.
- Novelty: a search on 2026-11-26 of the OEIS entry, arXiv abstracts and the
  web found only the one-directional remark (in the OEIS comment, and in a
  screening note of another project saying that the conjecture would force odd
  perfect numbers to be practical). MathSciNet, zbMATH and full texts of papers
  were not checked.

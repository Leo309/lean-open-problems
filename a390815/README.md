# OEIS A390815: σ(n) divides n! unless σ(n) is prime

Lean 4 proof of the following result.

[OEIS A390815](https://oeis.org/A390815) lists the denominators greater than 1
of the fractions `n!/σ(n)` in lowest terms, where `σ(n)` is the sum of the
divisors of `n`. The entry states two conjectures (C. H. R. Dequatre, 2026),
both checked there for `n ≤ 10^5`:

> Conjecture: all terms are prime.
>
> Conjecture: for `n ≥ 4`, if `σ(n)` does not divide `n!`, then `n` is a square.

It also records a question (R. J. Mathar, 2026): is this the same as
[A062700](https://oeis.org/A062700) (the prime values of `σ`) from the 3rd term
on?

**Results.**

- For every `n ≥ 1` with `n ≠ 3`: `σ(n)` divides `n!` if and only if `σ(n)` is
  not prime. The only exception is `n = 3`, where `σ(3) = 4` does not divide
  `3! = 6`.
- Hence for `n ≠ 3` the reduced denominator of `n!/σ(n)` is `σ(n)` when `σ(n)`
  is prime and `1` otherwise. For `n = 3` it is `2`. So both conjectures hold,
  and apart from the term `2` coming from `n = 3`, the terms of A390815 are
  exactly the prime values of `σ` in order of appearance, which is A062700.
- If `σ(n)` is prime and `n ≥ 3`, then `n` is an even power of a prime, in
  particular a square.

## Idea of the proof

Let `q^k` be a prime power dividing `σ(n)`.

- `k = 1`, `q ≤ n`: then `q` divides `n!`.
- `k = 1`, `q > n`: an induction over the factorization of `n`, using
  `σ(p^e) < 2p^e`, shows that `σ(n) = q`, so `σ(n)` is prime.
- `k ≥ 2`: every proper divisor of `n` is at most `n/2`, which gives
  `8σ(n) ≤ n^2 + 10n`. For `n ≥ 11` this yields `4q^k < n^2`, and that forces
  `kq ≤ n`. Then `q, 2q, …, kq` are `k` distinct factors of `n!`.

The cases `n ≤ 10` are checked directly. Conversely a prime value of `σ(n)` is
larger than `n` and cannot divide `n!`.

## Files

| File | Content |
| --- | --- |
| `A390815.lean` | Lean 4 formalization (about 350 lines). Imports `A017666` for the definition of `σ` and its multiplicativity |

## Checking the proof

From the repository root:

```
lake build A390815
```

Verified with Lean 4.36.0 and Mathlib v4.36.0. The build succeeds with no
`sorry`. Main theorems:

| Lean theorem | Statement |
| --- | --- |
| `sig_dvd_factorial_iff` | for `n ≥ 1`, `n ≠ 3`: `σ(n) ∣ n!` ⟺ `σ(n)` is not prime |
| `den_eq` | for `n ≠ 3` the reduced denominator is `σ(n)` if `σ(n)` is prime, else `1` |
| `conjecture1` | every reduced denominator other than 1 is prime |
| `conjecture2` | for `n ≥ 4`, `σ(n) ∤ n!` implies `n` is a square |
| `isSquare_of_prime_sig` | `σ(n)` prime and `n ≥ 3` imply `n` is a square |

Each of them depends only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## What is not claimed

- This is an elementary result. The fact may well be known in some form; it is
  recorded here because the OEIS entry lists it as two open conjectures and an
  open question.
- Novelty: the OEIS entries A390815, A390836 and A062700 (snapshot of
  2026-11-26) and a web search on 2026-11-27 show no proof. MathSciNet, zbMATH
  and full texts of papers were not checked.

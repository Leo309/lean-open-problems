/-
OEIS A390815: `σ(n)` divides `n!` unless `σ(n)` is prime.

OEIS A390815 lists the denominators greater than 1 of the fractions `n!/σ(n)` in lowest
terms, where `σ(n)` is the sum of the divisors of `n`. The entry records two conjectures
(C. H. R. Dequatre, 2026), both verified there for `n ≤ 10^5`:

  Conjecture 1: all terms are prime.
  Conjecture 2: for `n ≥ 4`, if `σ(n)` does not divide `n!`, then `n` is a square.

and a question (R. J. Mathar, 2026) whether the sequence agrees, after its first terms, with
A062700 (the prime values of `σ`).

This file proves, with no `sorry`:

* `sig_dvd_factorial_iff`: for every `n ≥ 1` with `n ≠ 3`, `σ(n) ∣ n!` if and only if `σ(n)`
  is not prime (for `n = 3`, `σ(3) = 4` does not divide `3! = 6`);
* `den_eq`: for `n ≠ 3` the reduced denominator of `n!/σ(n)` is `σ(n)` if `σ(n)` is prime and
  `1` otherwise, which answers the question about A062700;
* `conjecture1`: every reduced denominator different from 1 is prime;
* `conjecture2`: for `n ≥ 4`, if `σ(n) ∤ n!` then `n` is a square (indeed `σ(n)` is then
  prime, and `isSquare_of_prime_sig` shows that this forces `n` to be an even power of a
  prime).

Proof idea. Let `q^k` be a prime power dividing `σ(n)`. If `k = 1` and `q ≤ n` then
`q ∣ n!`. If `k = 1` and `q > n`, an induction over the factorization of `n` shows that
`σ(n) = q` (`large_prime`). If `k ≥ 2`, the bound `8 σ(n) ≤ n^2 + 10 n` gives
`4 q^k < n^2` for `n ≥ 11`, which forces `k q ≤ n`, and then `q, 2q, …, kq` are `k` distinct
factors of `n!`. The cases `n ≤ 10` are checked directly.

Checked with Lean 4.36.0 and Mathlib v4.36.0. Every theorem depends only on the axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/
import A017666
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD

open Finset

namespace A390815

open A017666

lemma sig_one : sig 1 = 1 := by decide

/-- `σ(n) ≥ n + 1` for `n ≥ 2`. -/
lemma succ_le_sig {n : ℕ} (hn : 2 ≤ n) : n + 1 ≤ sig n := by
  unfold sig
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rw [Nat.mem_divisors]
    rcases hd with rfl | rfl
    · exact ⟨one_dvd _, by omega⟩
    · exact ⟨dvd_rfl, by omega⟩
  have := Finset.sum_le_sum_of_subset (f := fun i => i) hsub
  rw [Finset.sum_pair (by omega : (1 : ℕ) ≠ n)] at this
  omega

/-- A quadratic bound: every proper divisor of `n` is at most `n / 2`. -/
lemma eight_sig_le {n : ℕ} (hn : 0 < n) : 8 * sig n ≤ n ^ 2 + 10 * n := by
  have hsub : n.divisors ⊆ insert n (range (n / 2 + 1)) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    obtain ⟨⟨k, hk⟩, -⟩ := hd
    rw [Finset.mem_insert, Finset.mem_range]
    by_cases hdn : d = n
    · exact Or.inl hdn
    · right
      have hk2 : 2 ≤ k := by
        by_contra h
        have : k = 0 ∨ k = 1 := by omega
        rcases this with rfl | rfl
        · simp at hk; omega
        · simp at hk; exact hdn hk.symm
      have : d * 2 ≤ n := by rw [hk]; exact Nat.mul_le_mul_left d hk2
      omega
  have h1 := Finset.sum_le_sum_of_subset (f := fun i => i) hsub
  rw [Finset.sum_insert (by rw [Finset.mem_range]; omega)] at h1
  have h2 := Finset.sum_range_id_mul_two (n / 2 + 1)
  simp only [Nat.add_sub_cancel] at h2
  have hm2 : 2 * (n / 2) ≤ n := by omega
  have h3 : (2 * (n / 2)) * (2 * (n / 2)) ≤ n * n := Nat.mul_le_mul hm2 hm2
  unfold sig
  nlinarith

lemma sq_le_two_pow : ∀ k : ℕ, 4 ≤ k → k ^ 2 ≤ 2 ^ k := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih => rw [pow_succ 2 k]; nlinarith

/-- If `q^k ≤ σ(n)` with `k ≥ 2` and `n ≥ 11`, then `k q ≤ n`. -/
lemma mul_le_of_pow_le {n q k : ℕ} (hq : 2 ≤ q) (hk : 2 ≤ k) (hn : 11 ≤ n)
    (h : q ^ k ≤ sig n) : k * q ≤ n := by
  have hb := eight_sig_le (by omega : 0 < n)
  have hnn : 11 * n ≤ n * n := Nat.mul_le_mul_right n hn
  have h4 : 4 * q ^ k < n ^ 2 := by nlinarith
  by_contra hcon
  rw [not_le] at hcon
  have h5 : n ^ 2 < (k * q) ^ 2 := Nat.pow_lt_pow_left hcon (by norm_num)
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  have h6 : 4 * q ^ j < (j + 2) ^ 2 := by
    have : 4 * q ^ j * q ^ 2 < (j + 2) ^ 2 * q ^ 2 := by
      calc 4 * q ^ j * q ^ 2 = 4 * q ^ (j + 2) := by ring
        _ < n ^ 2 := h4
        _ < ((j + 2) * q) ^ 2 := h5
        _ = (j + 2) ^ 2 * q ^ 2 := by ring
    exact lt_of_mul_lt_mul_right this (Nat.zero_le _)
  have h7 : 2 ^ j ≤ q ^ j := Nat.pow_le_pow_left hq j
  have h8 : 2 ^ (j + 2) < (j + 2) ^ 2 := by
    have : 2 ^ (j + 2) = 4 * 2 ^ j := by ring
    omega
  by_cases hj : 4 ≤ j + 2
  · exact absurd h8 (not_lt.mpr (sq_le_two_pow (j + 2) hj))
  · have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · norm_num at h8
    · norm_num at h6
      have : q = 2 := by omega
      subst this
      omega

/-- `q, 2q, …, kq` are `k` factors of `(kq)!`. -/
lemma pow_dvd_factorial_mul (q k : ℕ) (hq : 0 < q) : q ^ k ∣ Nat.factorial (k * q) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpos : 0 < (k + 1) * q := by positivity
    have e : (k + 1) * q = ((k + 1) * q - 1) + 1 := by omega
    have hle : k * q ≤ (k + 1) * q - 1 := by
      have : (k + 1) * q = k * q + q := by ring
      omega
    rw [e, Nat.factorial_succ, ← e, pow_succ, mul_comm (q ^ k) q]
    exact Nat.mul_dvd_mul (Dvd.intro_left (k + 1) rfl)
      (ih.trans (Nat.factorial_dvd_factorial hle))

lemma sum_pow_lt (p e : ℕ) (hp : 2 ≤ p) : ∑ j ∈ range (e + 1), p ^ j < 2 * p ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have := Nat.mul_le_mul_left (p ^ e) hp
    nlinarith

/-- A prime `q > n` dividing `σ(n)` equals `σ(n)`, and then `σ(n) < 2n`. -/
lemma large_prime : ∀ n : ℕ, 0 < n → ∀ q : ℕ, q.Prime → n < q → q ∣ sig n →
    sig n = q ∧ sig n < 2 * n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn q hq hnq hdiv
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have : n = 1 := by omega
    subst this
    rw [sig_one] at hdiv
    exact absurd (Nat.dvd_one.mp hdiv) hq.ne_one
  · obtain ⟨p, hp, hpn⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ n :=
      ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
    obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
    have he : e ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hnm
      exact hm (hnm ▸ hpn)
    subst hnm
    have hcop : Nat.Coprime (p ^ e) m :=
      Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
    have hm0 : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hn
      · exact h
    have hpe : 2 ≤ p ^ e :=
      calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos (by omega)
    have hlt : sig (p ^ e) < 2 * p ^ e := by
      rw [sig_prime_pow hp]; exact sum_pow_lt p e hp.two_le
    have hpos : 0 < sig (p ^ e) := sig_pos (by positivity)
    by_cases hm1 : m = 1
    · subst hm1
      rw [mul_one] at hdiv hnq ⊢
      obtain ⟨t, ht⟩ := hdiv
      have ht1 : t = 1 := by
        by_contra h
        rcases Nat.eq_zero_or_pos t with h0 | h0
        · subst h0; omega
        · have h2t : 2 ≤ t := by omega
          have := Nat.mul_le_mul_left q h2t
          omega
      subst ht1
      exact ⟨by omega, hlt⟩
    · exfalso
      have hm2 : 2 ≤ m := by omega
      have hmn : m < p ^ e * m := by nlinarith
      have h2pe : 2 * p ^ e ≤ p ^ e * m := by nlinarith
      have h2m : 2 * m ≤ p ^ e * m := by nlinarith
      rw [sig_mul hcop] at hdiv
      rcases (Nat.Prime.dvd_mul hq).mp hdiv with h | h
      · have := Nat.le_of_dvd hpos h
        omega
      · obtain ⟨h3, h4⟩ := ih m hmn hm0 q hq (by omega) h
        omega

/-- **Main theorem.** For `n ≥ 1`, `n ≠ 3`: `σ(n)` divides `n!` iff `σ(n)` is not prime. -/
theorem sig_dvd_factorial_iff {n : ℕ} (hn : 0 < n) (h3 : n ≠ 3) :
    sig n ∣ Nat.factorial n ↔ ¬ (sig n).Prime := by
  constructor
  · intro hd hprime
    rcases Nat.lt_or_ge n 2 with h | h
    · have : n = 1 := by omega
      subst this
      rw [sig_one] at hprime
      exact Nat.not_prime_one hprime
    · have := (Nat.Prime.dvd_factorial hprime).mp hd
      have := succ_le_sig h
      omega
  · intro hnp
    rcases Nat.lt_or_ge n 11 with hsmall | hbig
    · have v1 : sig 1 = 1 := by decide
      have v2 : sig 2 = 3 := by decide
      have v4 : sig 4 = 7 := by decide
      have v5 : sig 5 = 6 := by decide
      have v6 : sig 6 = 12 := by decide
      have v7 : sig 7 = 8 := by decide
      have v8 : sig 8 = 15 := by decide
      have v9 : sig 9 = 13 := by decide
      have v10 : sig 10 = 18 := by decide
      interval_cases n
      · rw [v1]; decide
      · exact absurd (by rw [v2]; norm_num : (sig 2).Prime) hnp
      · exact absurd rfl h3
      · exact absurd (by rw [v4]; norm_num : (sig 4).Prime) hnp
      · rw [v5]; decide
      · rw [v6]; decide
      · rw [v7]; decide
      · rw [v8]; decide
      · exact absurd (by rw [v9]; norm_num : (sig 9).Prime) hnp
      · rw [v10]; decide
    · rw [Nat.dvd_iff_prime_pow_dvd_dvd]
      intro q k hq hqk
      rcases Nat.lt_or_ge k 2 with hk | hk
      · have : k = 0 ∨ k = 1 := by omega
        rcases this with rfl | rfl
        · simp
        · rw [pow_one] at hqk ⊢
          rcases Nat.lt_or_ge n q with hlt | hle
          · exact absurd ((large_prime n hn q hq hlt hqk).1 ▸ hq) hnp
          · exact (Nat.Prime.dvd_factorial hq).mpr hle
      · have hle := Nat.le_of_dvd (sig_pos hn) hqk
        have := mul_le_of_pow_le hq.two_le hk hbig hle
        exact (pow_dvd_factorial_mul q k hq.pos).trans (Nat.factorial_dvd_factorial this)

/-! ### Prime values of `σ` occur only at even prime powers -/

lemma succ_dvd_sum_odd (p j : ℕ) : (p + 1) ∣ ∑ i ∈ range (2 * j + 1 + 1), p ^ i := by
  induction j with
  | zero => norm_num [Finset.sum_range_succ, add_comm]
  | succ j ih =>
    have e : 2 * (j + 1) + 1 + 1 = (2 * j + 1 + 1) + 1 + 1 := by ring
    rw [e, Finset.sum_range_succ, Finset.sum_range_succ, add_assoc]
    exact Dvd.dvd.add ih ⟨p ^ (2 * j + 1 + 1), by ring⟩

/-- If `σ(n)` is prime and `n ≥ 3`, then `n` is a square (an even power of a prime). -/
theorem isSquare_of_prime_sig {n : ℕ} (hn : 3 ≤ n) (h : (sig n).Prime) : IsSquare n := by
  obtain ⟨p, hp, hpn⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ n :=
    ⟨n.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd n⟩
  obtain ⟨e, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (by omega : n ≠ 0) p hp.ne_one
  have he : e ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hnm
    exact hm (hnm ▸ hpn)
  subst hnm
  have hcop : Nat.Coprime (p ^ e) m :=
    Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hp).2 hm)
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · subst h0; simp at hn
    · exact h0
  have hpe : 2 ≤ p ^ e :=
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right hp.pos (by omega)
  by_cases hm1 : m = 1
  · subst hm1
    rw [mul_one] at h hn ⊢
    rcases Nat.even_or_odd' e with ⟨j, rfl | rfl⟩
    · exact ⟨p ^ j, by ring⟩
    · exfalso
      rw [sig_prime_pow hp] at h
      rcases (Nat.dvd_prime h).mp (succ_dvd_sum_odd p j) with h1 | h1
      · have := hp.two_le; omega
      · rcases Nat.eq_zero_or_pos j with rfl | hj
        · norm_num at hn
          rw [← h1] at h
          have hodd : Odd p := hp.odd_of_ne_two (by omega)
          have h2 : 2 ∣ p + 1 := by
            obtain ⟨t, ht⟩ := hodd
            exact ⟨t + 1, by omega⟩
          rcases (Nat.dvd_prime h).mp h2 with h2 | h2 <;> omega
        · have hsub : range 3 ⊆ range (2 * j + 1 + 1) := by
            intro i hi
            rw [Finset.mem_range] at hi ⊢
            omega
          have h5 := Finset.sum_le_sum_of_subset (f := fun i => p ^ i) hsub
          have h6 : ∑ i ∈ range 3, p ^ i = 1 + p + p ^ 2 := by
            simp [Finset.sum_range_succ]
          have h7 : 0 < p ^ 2 := pow_pos hp.pos 2
          omega
  · exfalso
    have hm2 : 2 ≤ m := by omega
    rw [sig_mul hcop] at h
    have a1 := succ_le_sig hpe
    have a2 := succ_le_sig hm2
    exact Nat.not_prime_mul (by omega) (by omega) h

/-! ### The OEIS statements -/

/-- Denominator of `n!/σ(n)` in lowest terms. -/
def den (n : ℕ) : ℕ := sig n / Nat.gcd (sig n) (Nat.factorial n)

/-- For `n ≠ 3` the reduced denominator of `n!/σ(n)` is `σ(n)` when `σ(n)` is prime and `1`
otherwise. Hence the terms of A390815 other than the term `2` coming from `n = 3` are exactly
the prime values of `σ` in order of appearance (A062700). -/
theorem den_eq {n : ℕ} (hn : 0 < n) (h3 : n ≠ 3) :
    den n = if (sig n).Prime then sig n else 1 := by
  unfold den
  split_ifs with hp
  · have hnd : ¬ sig n ∣ Nat.factorial n := fun hd => (sig_dvd_factorial_iff hn h3).mp hd hp
    have hc : Nat.Coprime (sig n) (Nat.factorial n) := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
    rw [Nat.Coprime] at hc
    rw [hc, Nat.div_one]
  · have hd := (sig_dvd_factorial_iff hn h3).mpr hp
    rw [Nat.gcd_eq_left hd, Nat.div_self (sig_pos hn)]

lemma den_three : den 3 = 2 := by
  unfold den
  rw [show sig 3 = 4 by decide]
  decide

/-- **Conjecture 1 of A390815.** Every denominator greater than 1 is prime. -/
theorem conjecture1 {n : ℕ} (hn : 0 < n) (h : den n ≠ 1) : (den n).Prime := by
  by_cases h3 : n = 3
  · subst h3; rw [den_three]; exact Nat.prime_two
  · rw [den_eq hn h3] at h ⊢
    split_ifs with hp
    · exact hp
    · simp [hp] at h

/-- **Conjecture 2 of A390815.** For `n ≥ 4`, if `σ(n)` does not divide `n!` then `n` is a
square. -/
theorem conjecture2 {n : ℕ} (hn : 4 ≤ n) (h : ¬ sig n ∣ Nat.factorial n) : IsSquare n := by
  apply isSquare_of_prime_sig (by omega)
  by_contra hnp
  exact h ((sig_dvd_factorial_iff (by omega) (by omega)).mpr hnp)

end A390815

#print axioms A390815.sig_dvd_factorial_iff
#print axioms A390815.den_eq
#print axioms A390815.conjecture1
#print axioms A390815.conjecture2

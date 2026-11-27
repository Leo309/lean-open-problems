/-
OEIS A050972 / A050973 (friendly pairs) and practical numbers: Coleman's conjecture is false.

Two positive integers `a < b` form a *friendly pair* if they have the same abundancy index,
`σ(a)/a = σ(b)/b`. OEIS A050972 lists the smaller members and A050973 the larger members of
all friendly pairs. The entry A050972 records (J. Coleman, 2014):

  Conjecture: if `a(n)` is in A005153 (practical numbers), then `A050973(n)` is in A005153.

In other words: if the smaller member of a friendly pair is practical, so is the larger one.

This file proves, with no `sorry`, that the conjecture is false:

* `counterexample_42_544635`: `(42, 544635)` is a friendly pair (common abundancy `16/7`),
  `42` is practical and `544635 = 3^2 * 5 * 7^2 * 13 * 19` is odd, hence not practical;
* `infinitely_many_counterexamples`: `(42 * 11^j, 544635 * 11^j)` is a counterexample for
  every `j`;
* `even_counterexample`: `(13479018, 21180250)` is a counterexample in which both members are
  even, so restricting the conjecture to even numbers does not rescue it;
* `not_colemanFriendlyConjecture`: the conjecture, stated for all friendly pairs, fails.

The pair `(42, 544635)` is a classical example of a friendly pair of opposite parity. A
computer search outside Lean (not part of the verified statement) shows that it is the
counterexample with the smallest larger member, and the only one with larger member below
`3 * 10^6`.

Checked with Lean 4.36.0 and Mathlib v4.36.0. Every theorem depends only on the axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/
import A017666
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD

open Finset

namespace A050972

open A017666

/-- `a` and `b` have the same abundancy index: `σ(a)/a = σ(b)/b`, written without division. -/
def Friendly (a b : ℕ) : Prop := sig a * b = sig b * a

/-- Coleman's conjecture on A050972: in a friendly pair `a < b`, if `a` is practical then so
is `b`. -/
def ColemanFriendlyConjecture : Prop :=
  ∀ a b : ℕ, 0 < a → a < b → Friendly a b → A5153 a → A5153 b

/-- A lower bound for `slo n p` from any set of divisors of `n` that are smaller than `p`. -/
lemma le_slo {n p : ℕ} (S : Finset ℕ) (hS : ∀ e ∈ S, e ∣ n ∧ e < p ∧ 0 < e) (hn : n ≠ 0) :
    ∑ e ∈ S, e ≤ slo n p := by
  classical
  unfold slo
  apply Finset.sum_le_sum_of_subset
  intro e he
  obtain ⟨h1, h2, h3⟩ := hS e he
  rw [Finset.mem_filter, Nat.mem_divisors]
  refine ⟨⟨h1, hn⟩, fun r hr hre => ?_⟩
  exact lt_of_le_of_lt (Nat.le_of_dvd h3 hre) h2

/-- A practical number from Stewart's criterion. -/
lemma practical_of_stewart {n : ℕ} (hn : 0 < n)
    (H : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ 1 + slo n p) : A5153 n :=
  ⟨hn, (SC_of_stewart n hn H).practical hn⟩

lemma sig_42 : sig 42 = 96 := by decide

lemma sig_544635 : sig 544635 = 1244880 := by
  have e : (544635 : ℕ) = 9 * (5 * (49 * (13 * 19))) := by norm_num
  have h9 : sig 9 = 13 := by decide
  have h5 : sig 5 = 6 := by decide
  have h49 : sig 49 = 57 := by decide
  have h13 : sig 13 = 14 := by decide
  have h19 : sig 19 = 20 := by decide
  rw [e, sig_mul (by norm_num), sig_mul (by norm_num), sig_mul (by norm_num),
    sig_mul (by norm_num), h9, h5, h49, h13, h19]

/-- Primes dividing `42 * 11 ^ j` are among `2, 3, 7, 11`. -/
lemma prime_dvd_42_mul {p j : ℕ} (hp : p.Prime) (h : p ∣ 42 * 11 ^ j) :
    p = 2 ∨ p = 3 ∨ p = 7 ∨ p = 11 := by
  have e : (42 : ℕ) = 2 * (3 * 7) := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    · rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h))
      · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h)))
  · have := hp.dvd_of_dvd_pow h
    exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp this)))

/-- `42 * 11 ^ j` is practical. -/
lemma practical_42_mul (j : ℕ) : A5153 (42 * 11 ^ j) := by
  have hpos : 0 < 42 * 11 ^ j := by positivity
  have h42 : (42 : ℕ) ∣ 42 * 11 ^ j := Dvd.intro _ rfl
  refine practical_of_stewart hpos fun p hp hpd => ?_
  have hd : ∀ e : ℕ, e ∣ 42 → e ∣ 42 * 11 ^ j := fun e he => he.trans h42
  rcases prime_dvd_42_mul hp hpd with rfl | rfl | rfl | rfl
  · have := le_slo (n := 42 * 11 ^ j) (p := 2) {1}
      (by intro e he; simp at he; subst he; exact ⟨one_dvd _, by norm_num, by norm_num⟩)
      hpos.ne'
    simp at this; omega
  · have := le_slo (n := 42 * 11 ^ j) (p := 3) {1, 2}
      (by
        intro e he
        simp at he
        rcases he with rfl | rfl
        · exact ⟨one_dvd _, by norm_num, by norm_num⟩
        · exact ⟨hd 2 (by norm_num), by norm_num, by norm_num⟩)
      hpos.ne'
    simp at this; omega
  · have := le_slo (n := 42 * 11 ^ j) (p := 7) {1, 2, 3}
      (by
        intro e he
        simp at he
        rcases he with rfl | rfl | rfl
        · exact ⟨one_dvd _, by norm_num, by norm_num⟩
        · exact ⟨hd 2 (by norm_num), by norm_num, by norm_num⟩
        · exact ⟨hd 3 (by norm_num), by norm_num, by norm_num⟩)
      hpos.ne'
    simp at this; omega
  · have := le_slo (n := 42 * 11 ^ j) (p := 11) {1, 2, 3, 6}
      (by
        intro e he
        simp at he
        rcases he with rfl | rfl | rfl | rfl
        · exact ⟨one_dvd _, by norm_num, by norm_num⟩
        · exact ⟨hd 2 (by norm_num), by norm_num, by norm_num⟩
        · exact ⟨hd 3 (by norm_num), by norm_num, by norm_num⟩
        · exact ⟨hd 6 (by norm_num), by norm_num, by norm_num⟩)
      hpos.ne'
    simp at this; omega

/-- **Infinitely many counterexamples.** For every `j`, `(42 * 11^j, 544635 * 11^j)` is a
friendly pair whose smaller member is practical and whose larger member is not. -/
theorem infinitely_many_counterexamples (j : ℕ) :
    0 < 42 * 11 ^ j ∧ 42 * 11 ^ j < 544635 * 11 ^ j ∧
      Friendly (42 * 11 ^ j) (544635 * 11 ^ j) ∧
      A5153 (42 * 11 ^ j) ∧ ¬ A5153 (544635 * 11 ^ j) := by
  have hpow : 0 < 11 ^ j := by positivity
  refine ⟨by positivity, by nlinarith, ?_, practical_42_mul j, ?_⟩
  · have c1 : Nat.Coprime 42 (11 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
    have c2 : Nat.Coprime 544635 (11 ^ j) := Nat.Coprime.pow_right _ (by norm_num)
    unfold Friendly
    rw [sig_mul c1, sig_mul c2, sig_42, sig_544635]
    ring
  · apply not_practical_of_odd
    · exact Odd.mul (by decide) (Odd.pow (by decide))
    · have : 544635 ≤ 544635 * 11 ^ j := Nat.le_mul_of_pos_right _ hpow
      omega

/-- **The smallest counterexample.** `(42, 544635)` is a friendly pair, `42` is practical and
`544635` is not. -/
theorem counterexample_42_544635 :
    Friendly 42 544635 ∧ A5153 42 ∧ ¬ A5153 544635 := by
  have h := infinitely_many_counterexamples 0
  simp only [pow_zero, mul_one] at h
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- **Coleman's conjecture on A050972 is false.** -/
theorem not_colemanFriendlyConjecture : ¬ ColemanFriendlyConjecture := by
  intro H
  obtain ⟨h1, h2, h3⟩ := counterexample_42_544635
  exact h3 (H 42 544635 (by norm_num) (by norm_num) h1 h2)

/-! ### A counterexample with both members even -/

lemma sig_13479018 : sig 13479018 = 33357312 := by
  have e : (13479018 : ℕ) = 2 * (3 * (49 * (361 * 127))) := by norm_num
  have h2 : sig 2 = 3 := by decide
  have h3 : sig 3 = 4 := by decide
  have h49 : sig 49 = 57 := by decide
  have h361 : sig 361 = 381 := by
    have := sig_prime_pow (p := 19) (by norm_num) 2
    norm_num [Finset.sum_range_succ] at this
    exact this
  have h127 : sig 127 = 128 := by
    have := sig_prime_pow (p := 127) (by norm_num) 1
    norm_num [Finset.sum_range_succ] at this
    exact this
  rw [e, sig_mul (by norm_num), sig_mul (by norm_num), sig_mul (by norm_num),
    sig_mul (by norm_num), h2, h3, h49, h361, h127]

lemma sig_21180250 : sig 21180250 = 52416000 := by
  have e : (21180250 : ℕ) = 2 * (125 * (343 * (13 * 19))) := by norm_num
  have h2 : sig 2 = 3 := by decide
  have h125 : sig 125 = 156 := by
    have := sig_prime_pow (p := 5) (by norm_num) 3
    norm_num [Finset.sum_range_succ] at this
    exact this
  have h343 : sig 343 = 400 := by
    have := sig_prime_pow (p := 7) (by norm_num) 3
    norm_num [Finset.sum_range_succ] at this
    exact this
  have h13 : sig 13 = 14 := by decide
  have h19 : sig 19 = 20 := by decide
  rw [e, sig_mul (by norm_num), sig_mul (by norm_num), sig_mul (by norm_num),
    sig_mul (by norm_num), h2, h125, h343, h13, h19]

lemma prime_dvd_13479018 {p : ℕ} (hp : p.Prime) (h : p ∣ 13479018) :
    p = 2 ∨ p = 3 ∨ p = 7 ∨ p = 19 ∨ p = 127 := by
  have e : (13479018 : ℕ) = 2 * (3 * (7 ^ 2 * (19 ^ 2 * 127))) := by norm_num
  rw [e] at h
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h))
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact Or.inr (Or.inr (Or.inl
      ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h))))
  rcases (Nat.Prime.dvd_mul hp).mp h with h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp (hp.dvd_of_dvd_pow h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h))))

lemma practical_13479018 : A5153 13479018 := by
  refine practical_of_stewart (by norm_num) fun p hp hpd => ?_
  have key : ∀ (S : Finset ℕ) (q : ℕ), (∀ e ∈ S, e ∣ 13479018 ∧ e < q ∧ 0 < e) →
      ∑ e ∈ S, e ≤ slo 13479018 q := fun S q hS => le_slo S hS (by norm_num)
  rcases prime_dvd_13479018 hp hpd with rfl | rfl | rfl | rfl | rfl
  · have := key {1} 2 (by intro e he; simp at he; subst he; norm_num)
    simp at this; omega
  · have := key {1, 2} 3 (by
      intro e he; simp at he
      rcases he with rfl | rfl <;> norm_num)
    simp at this; omega
  · have := key {1, 2, 3} 7 (by
      intro e he; simp at he
      rcases he with rfl | rfl | rfl <;> norm_num)
    simp at this; omega
  · have := key {1, 2, 3, 6, 7} 19 (by
      intro e he; simp at he
      rcases he with rfl | rfl | rfl | rfl | rfl <;> norm_num)
    simp at this; omega
  · have := key {1, 2, 3, 6, 7, 14, 21, 42, 49} 127 (by
      intro e he; simp at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num)
    simp at this; omega

lemma not_practical_21180250 : ¬ A5153 21180250 := by
  rintro ⟨hpos, hpr⟩
  have h := practical_prime_le hpos hpr (q := 5) (by norm_num) (by norm_num)
  have hsub : (Nat.divisors 21180250).filter (· < 5) ⊆ {1, 2} := by
    intro e he
    rw [Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨hd, -⟩, hlt⟩ := he
    have h0 : e ≠ 0 := by rintro rfl; simp at hd
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases e
    · exact absurd rfl h0
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd hd (by norm_num)
    · exact absurd hd (by norm_num)
  have := Finset.sum_le_sum_of_subset (f := fun i => i) hsub
  simp at this
  omega

/-- A counterexample in which both members are even: `(13479018, 21180250)` is a friendly
pair (common abundancy `2304/931`), `13479018 = 2 * 3 * 7^2 * 19^2 * 127` is practical and
`21180250 = 2 * 5^3 * 7^3 * 13 * 19` is not. -/
theorem even_counterexample :
    Even 13479018 ∧ Even 21180250 ∧ 13479018 < 21180250 ∧ Friendly 13479018 21180250 ∧
      A5153 13479018 ∧ ¬ A5153 21180250 := by
  refine ⟨by decide, by decide, by norm_num, ?_, practical_13479018, not_practical_21180250⟩
  unfold Friendly
  rw [sig_13479018, sig_21180250]

end A050972

#print axioms A050972.not_colemanFriendlyConjecture
#print axioms A050972.infinitely_many_counterexamples
#print axioms A050972.even_counterexample

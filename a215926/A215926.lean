/-
OEIS A215926: a(n) = smallest deficient k such that k * n is non-deficient.

Conjectures recorded in the OEIS entry (2012) and stated formally in
google-deepmind/formal-conjectures (`FormalConjectures/OEIS/215926.lean`):

* `conjecture_1`: for every n ≥ 2, a(n) is 1, 3 or a power of 2;
* `conjecture_2`: for m ≥ 1, the first n ≥ 2 with a(n) = 2^m is the least prime above 2^m.

This file proves, with no `sorry`:

* unconditionally, a(n) ∈ {1, 2, 3} for even n, and for odd n ≥ 3 the value a(n) is either a
  power of 2 or an almost perfect number (σ(k) = 2k - 1), and a(n) ≤ n;
* hence both conjectures follow from the classical conjecture that every almost perfect
  number is a power of 2 (`AlmostPerfectNumbers.exists_almost_perfect_not_power_of_two`
  in formal-conjectures asks whether this fails);
* bounded versions: `conjecture_1` holds for all n ≤ N as soon as there is no almost perfect
  number ≤ N other than powers of 2, and similarly `conjecture_2` for m with bound 2^m;
* the "lower bound" half of `conjecture_2` is unconditional;
* unconditional small cases: `conjecture_1` for 2 ≤ n < 256 and `conjecture_2` for 1 ≤ m ≤ 8;
* the converse for Conjecture 1 (`almostPerfect_of_conjecture_1`): if some almost perfect
  number is not a power of 2, the least such number is a value of `a`, so `conjecture_1`
  fails. Hence `conjecture_1_iff_almostPerfect`: Conjecture 1 is *equivalent* to the almost
  perfect number conjecture. The proof uses the divergence of the sum of prime reciprocals.

Checked with Lean 4.36.0 and Mathlib v4.36.0. Every theorem depends only on the axioms
`propext`, `Classical.choice`, `Quot.sound`.

The definitions `a`, `nextPrimeTwoPow`, `AlmostPerfect` are copied verbatim from
formal-conjectures.
-/
import Mathlib.NumberTheory.FactorisationProperties
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum.Prime

open scoped ArithmeticFunction.sigma

namespace OeisA215926

/-- Smallest deficient number `k` such that `k * n` is non-deficient (perfect or abundant). -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | k.Deficient ∧ ((k * n).Perfect ∨ (k * n).Abundant)}

/-- The smallest prime strictly greater than `2 ^ m` (OEIS A014210). -/
noncomputable def nextPrimeTwoPow (m : ℕ) : ℕ :=
  sInf {p : ℕ | 2 ^ m < p ∧ p.Prime}

/-- A number is almost perfect if the sum of its divisors is equal to `2 * n - 1`. -/
def AlmostPerfect (n : ℕ) : Prop :=
  1 + σ 1 n = 2 * n

/-! ### The sum of divisors -/

/-- Sum of all divisors. -/
def S (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- The set whose infimum defines `a n`. -/
def T (n : ℕ) : Set ℕ := {k : ℕ | k.Deficient ∧ ((k * n).Perfect ∨ (k * n).Abundant)}

lemma a_def (n : ℕ) : a n = sInf (T n) := rfl

lemma S_eq (n : ℕ) : S n = (∑ i ∈ n.properDivisors, i) + n :=
  Nat.sum_divisors_eq_sum_properDivisors_add_self

lemma deficient_iff (k : ℕ) : k.Deficient ↔ S k < 2 * k := by
  unfold Nat.Deficient
  rw [S_eq]
  omega

lemma nd_iff (m : ℕ) : (m.Perfect ∨ m.Abundant) ↔ 0 < m ∧ 2 * m ≤ S m := by
  rw [S_eq]
  constructor
  · rintro (h | h)
    · obtain ⟨h1, h2⟩ := h
      omega
    · have := h.pos
      unfold Nat.Abundant at h
      omega
  · rintro ⟨h1, h2⟩
    by_cases h : ∑ i ∈ m.properDivisors, i = m
    · exact Or.inl ⟨h, h1⟩
    · right
      unfold Nat.Abundant
      omega

lemma almostPerfect_iff (k : ℕ) : AlmostPerfect k ↔ S k + 1 = 2 * k := by
  unfold AlmostPerfect S
  rw [ArithmeticFunction.sigma_one_apply]
  omega

lemma mem_iff (n k : ℕ) : k ∈ T n ↔ S k < 2 * k ∧ 0 < k * n ∧ 2 * (k * n) ≤ S (k * n) := by
  simp only [T, Set.mem_ofPred_eq, deficient_iff, nd_iff]

/-- If `r` is a divisor of `n` other than `n`, then `σ(n) ≥ n + r`. -/
lemma S_ge_add {n r : ℕ} (hn : 0 < n) (hr : r ∣ n) (hne : r ≠ n) : n + r ≤ S n := by
  have hsub : ({n, r} : Finset ℕ) ⊆ n.divisors := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with h | h
    · rw [h]; exact Nat.mem_divisors.2 ⟨dvd_rfl, hn.ne'⟩
    · rw [h]; exact Nat.mem_divisors.2 ⟨hr, hn.ne'⟩
  have h := Finset.sum_le_sum_of_subset (f := fun d : ℕ => d) hsub
  rw [Finset.sum_pair (Ne.symm hne)] at h
  exact h

/-- `σ(2^j) = 2^(j+1) - 1`. -/
lemma S_two_pow (j : ℕ) : S (2 ^ j) + 1 = 2 ^ (j + 1) := by
  unfold S
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ]
    have : 2 ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
    omega

/-- `σ(2^j n) = σ(2^j) σ(n)` for odd `n`. -/
lemma S_two_pow_mul (j : ℕ) {n : ℕ} (hodd : Odd n) : S (2 ^ j * n) = S (2 ^ j) * S n := by
  unfold S
  exact Nat.Coprime.sum_divisors_mul (Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hodd))

/-- Submultiplicativity: `σ(k n) ≤ σ(k) σ(n)`. -/
lemma S_mul_le (k n : ℕ) : S (k * n) ≤ S k * S n := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [S]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [S]
  unfold S
  rw [Finset.sum_mul_sum, ← Finset.sum_product']
  have hmaps : ∀ p ∈ k.divisors ×ˢ n.divisors, p.1 * p.2 ∈ (k * n).divisors := by
    intro p hp
    rw [Finset.mem_product, Nat.mem_divisors, Nat.mem_divisors] at hp
    exact Nat.mem_divisors.2 ⟨Nat.mul_dvd_mul hp.1.1 hp.2.1, (Nat.mul_pos hk hn).ne'⟩
  have key := Finset.sum_fiberwise_of_maps_to hmaps (fun p : ℕ × ℕ => p.1 * p.2)
  rw [← key]
  apply Finset.sum_le_sum
  intro d hd
  obtain ⟨k₁, k₂, h1, h2, rfl⟩ := Nat.dvd_mul.1 (Nat.mem_divisors.1 hd).1
  have hmem : (k₁, k₂) ∈
      Finset.filter (fun p : ℕ × ℕ => p.1 * p.2 = k₁ * k₂) (k.divisors ×ˢ n.divisors) := by
    simp [Nat.mem_divisors, h1, h2, hk.ne', hn.ne']
  exact Finset.single_le_sum (f := fun p : ℕ × ℕ => p.1 * p.2) (fun _ _ => Nat.zero_le _) hmem

/-- `σ(m) t ≤ σ(m t)` for `t > 0`. -/
lemma S_mul_ge (m : ℕ) {t : ℕ} (ht : 0 < t) : S m * t ≤ S (m * t) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [S]
  unfold S
  calc (∑ d ∈ m.divisors, d) * t = ∑ d ∈ m.divisors, d * t := Finset.sum_mul _ _ _
    _ = ∑ x ∈ m.divisors.image (fun d => d * t), x :=
        (Finset.sum_image (f := fun x : ℕ => x)
          (fun x _ y _ h => Nat.eq_of_mul_eq_mul_right ht h)).symm
    _ ≤ ∑ x ∈ (m * t).divisors, x := by
        apply Finset.sum_le_sum_of_subset
        intro x hx
        obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 hx
        exact Nat.mem_divisors.2
          ⟨Nat.mul_dvd_mul_right (Nat.mem_divisors.1 hd).1 t, (Nat.mul_pos hm ht).ne'⟩

/-! ### Basic facts about `a n` -/

lemma a_mem {n : ℕ} (h : (T n).Nonempty) : a n ∈ T n := Nat.sInf_mem h

lemma a_le {n k : ℕ} (h : k ∈ T n) : a n ≤ k := Nat.sInf_le h

lemma not_mem_of_lt {n k : ℕ} (h : k < a n) : k ∉ T n := fun hk =>
  absurd (a_le hk) (by omega)

/-- Membership of a power of two, for odd `n`. -/
lemma two_pow_mem_iff (j : ℕ) {n : ℕ} (hn : 0 < n) (hodd : Odd n) :
    2 ^ j ∈ T n ↔ (S (2 ^ j) + 1) * n ≤ S (2 ^ j) * S n := by
  rw [mem_iff, S_two_pow_mul j hodd]
  have h1 := S_two_pow j
  have h2 : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have h3 : 0 < 2 ^ j * n := Nat.mul_pos (by positivity) hn
  have h4 : 2 * (2 ^ j * n) = (S (2 ^ j) + 1) * n := by rw [h1, h2]; ring
  rw [h4]
  constructor
  · rintro ⟨_, _, h⟩
    exact h
  · intro h
    exact ⟨by omega, h3, h⟩

/-! ### Even `n` -/

lemma S_six : S 6 = 12 := by decide

lemma three_mem {n : ℕ} (hn : 0 < n) (he : Even n) : 3 ∈ T n := by
  rw [mem_iff]
  obtain ⟨t, rfl⟩ := he
  have ht : 0 < t := by omega
  refine ⟨(deficient_iff 3).1 Nat.deficient_three, by omega, ?_⟩
  have h := S_mul_ge 6 ht
  rw [S_six] at h
  have e : 3 * (t + t) = 6 * t := by ring
  rw [e]
  omega

/-- For even `n`, `a n ∈ {1, 2, 3}` (unconditionally). -/
theorem a_even {n : ℕ} (hn : 0 < n) (he : Even n) : a n = 1 ∨ a n = 2 ∨ a n = 3 := by
  have h3 := three_mem hn he
  have hle := a_le h3
  have hmem := a_mem ⟨3, h3⟩
  rw [mem_iff] at hmem
  omega

/-! ### Odd `n` -/

/-- For odd `n ≥ 3`, the power of two `2 ^ ⌊log₂ n⌋` is admissible. -/
lemma two_pow_log_mem {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) : 2 ^ Nat.log 2 n ∈ T n := by
  have hn0 : 0 < n := by omega
  rw [two_pow_mem_iff _ hn0 hodd]
  have h1 := S_two_pow (Nat.log 2 n)
  have h2 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have h3 : n + 1 ≤ S n := S_ge_add hn0 (one_dvd n) (by omega)
  set B := S (2 ^ Nat.log 2 n) with hB
  have hnB : n ≤ B := by omega
  calc (B + 1) * n = B * n + n := by ring
    _ ≤ B * n + B := by omega
    _ = B * (n + 1) := by ring
    _ ≤ B * S n := Nat.mul_le_mul_left B h3

lemma a_le_self {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) : a n ≤ n :=
  (a_le (two_pow_log_mem hn hodd)).trans (Nat.pow_log_le_self 2 (by omega))

/-- The arithmetic heart of the argument. -/
lemma arith_key {k n s c B : ℕ} (hn : 0 < n) (hc : c + 2 ≤ 2 * k)
    (h1 : 2 * (k * n) ≤ c * s) (h2 : B * s < (B + 1) * n) (hkB : k ≤ B) : False := by
  obtain ⟨t, rfl⟩ : ∃ t, k = t + 1 := ⟨k - 1, by omega⟩
  have hct : c ≤ 2 * t := by omega
  have h3 : (t + 1) * n ≤ t * s := by
    have h : c * s ≤ 2 * (t * s) := by
      calc c * s ≤ (2 * t) * s := Nat.mul_le_mul_right s hct
        _ = 2 * (t * s) := by ring
    omega
  have h6 : B * (t + 1) * n ≤ t * (B + 1) * n := by
    calc B * (t + 1) * n = B * ((t + 1) * n) := by ring
      _ ≤ B * (t * s) := Nat.mul_le_mul_left B h3
      _ = t * (B * s) := by ring
      _ ≤ t * ((B + 1) * n) := Nat.mul_le_mul_left t h2.le
      _ = t * (B + 1) * n := by ring
  have h7 : B * (t + 1) ≤ t * (B + 1) := Nat.le_of_mul_le_mul_right h6 hn
  have e1 : B * (t + 1) = B * t + B := by ring
  have e2 : t * (B + 1) = B * t + t := by ring
  omega

/-- **Main lemma.** For odd `n ≥ 3`, `a n` is a power of two or an almost perfect number. -/
theorem a_odd {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    (∃ j, a n = 2 ^ j) ∨ AlmostPerfect (a n) := by
  have hn0 : 0 < n := by omega
  have hmem := a_mem ⟨_, two_pow_log_mem hn hodd⟩
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hpow, hap⟩ := hcon
  rw [mem_iff] at hmem
  obtain ⟨hdef, -, hnd⟩ := hmem
  have hk0 : a n ≠ 0 := by
    intro h
    rw [h] at hdef
    omega
  have hj1 : 2 ^ Nat.log 2 (a n) ≤ a n := Nat.pow_log_le_self 2 hk0
  have hj2 : a n < 2 ^ (Nat.log 2 (a n) + 1) := Nat.lt_pow_succ_log_self (by norm_num) (a n)
  have hj3 : 2 ^ Nat.log 2 (a n) < a n :=
    lt_of_le_of_ne hj1 (fun h => hpow ⟨Nat.log 2 (a n), h.symm⟩)
  have hnot := not_mem_of_lt hj3
  rw [two_pow_mem_iff _ hn0 hodd, not_le] at hnot
  have hB := S_two_pow (Nat.log 2 (a n))
  rw [almostPerfect_iff] at hap
  exact arith_key hn0 (c := S (a n)) (by omega) (hnd.trans (S_mul_le _ _)) hnot (by omega)

/-! ### Conjecture 1 -/

/-- Unconditional form: for every `n ≥ 2`, `a n` is `1`, `3`, a power of two,
or an almost perfect number which is at most `n`. -/
theorem conjecture_1_unconditional (n : ℕ) (hn : 2 ≤ n) :
    a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo ∨ (AlmostPerfect (a n) ∧ a n ≤ n) := by
  rcases Nat.even_or_odd n with he | ho
  · rcases a_even (by omega) he with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl ⟨1, by rw [h]⟩))
    · exact Or.inr (Or.inl h)
  · have hn3 : 3 ≤ n := by
      obtain ⟨t, rfl⟩ := ho
      omega
    rcases a_odd hn3 ho with ⟨j, hj⟩ | h
    · exact Or.inr (Or.inr (Or.inl ⟨j, hj⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h, a_le_self hn3 ho⟩))

/-- Bounded form: if every almost perfect number `≤ N` is a power of two, then
`conjecture_1` holds for all `2 ≤ n ≤ N`. -/
theorem conjecture_1_of_bound (N : ℕ) (H : ∀ k ≤ N, AlmostPerfect k → ∃ j, k = 2 ^ j)
    (n : ℕ) (hn : 2 ≤ n) (hN : n ≤ N) :
    a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo := by
  rcases conjecture_1_unconditional n hn with h | h | h | ⟨h, hle⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inr (H _ (hle.trans hN) h))

/-- **A215926 Conjecture 1 follows from the almost perfect number conjecture.** -/
theorem conjecture_1_of_almostPerfect (H : ∀ k, AlmostPerfect k → ∃ j, k = 2 ^ j)
    (n : ℕ) (hn : 2 ≤ n) :
    a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo :=
  conjecture_1_of_bound n (fun k _ hk => H k hk) n hn le_rfl

/-! ### Conjecture 2 -/

lemma two_le_two_pow {m : ℕ} (hm : 1 ≤ m) : 2 ≤ 2 ^ m := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm

lemma nextPrime_spec (m : ℕ) : 2 ^ m < nextPrimeTwoPow m ∧ (nextPrimeTwoPow m).Prime := by
  obtain ⟨p, hp, h1, _⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ m) (by positivity)
  exact Nat.sInf_mem (s := {p : ℕ | 2 ^ m < p ∧ p.Prime}) ⟨p, h1, hp⟩

lemma nextPrime_le {m q : ℕ} (h1 : 2 ^ m < q) (hq : q.Prime) : nextPrimeTwoPow m ≤ q :=
  Nat.sInf_le (s := {p : ℕ | 2 ^ m < p ∧ p.Prime}) ⟨h1, hq⟩

/-- By Bertrand's postulate the least prime above `2 ^ m` is below `2 ^ (m + 1)`. -/
lemma nextPrime_lt (m : ℕ) (hm : 1 ≤ m) : nextPrimeTwoPow m < 2 ^ (m + 1) := by
  obtain ⟨q, hq, h1, h2⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ m) (by positivity)
  have hle := nextPrime_le h1 hq
  obtain ⟨hgt, hp⟩ := nextPrime_spec m
  have e : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
  have h2m := two_le_two_pow hm
  have hne : nextPrimeTwoPow m ≠ 2 ^ (m + 1) := by
    intro h
    have h2dvd : 2 ∣ nextPrimeTwoPow m := by
      rw [h]
      exact dvd_pow_self 2 (by omega)
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2dvd
    omega
  omega

lemma S_prime {p : ℕ} (hp : p.Prime) : S p = p + 1 := by
  unfold S
  rw [hp.divisors, Finset.sum_pair hp.one_lt.ne]
  omega

/-- If no almost perfect number below `2 ^ m` other than powers of two exists, then
`a(p) = 2 ^ m` for the least prime `p > 2 ^ m`. -/
theorem a_nextPrime (m : ℕ) (hm : 1 ≤ m)
    (H : ∀ k < 2 ^ m, AlmostPerfect k → ∃ j, k = 2 ^ j) :
    a (nextPrimeTwoPow m) = 2 ^ m := by
  obtain ⟨hgt, hp⟩ := nextPrime_spec m
  have hlt := nextPrime_lt m hm
  have h2m := two_le_two_pow hm
  generalize nextPrimeTwoPow m = p at *
  have hodd : Odd p := by
    rcases hp.eq_two_or_odd' with h | h
    · omega
    · exact h
  have hp3 : 3 ≤ p := by omega
  have hp0 : 0 < p := by omega
  have hSp := S_prime hp
  have hmemm : 2 ^ m ∈ T p := by
    rw [two_pow_mem_iff _ hp0 hodd, hSp]
    have hB := S_two_pow m
    have hpB : p ≤ S (2 ^ m) := by omega
    calc (S (2 ^ m) + 1) * p = S (2 ^ m) * p + p := by ring
      _ ≤ S (2 ^ m) * p + S (2 ^ m) := by omega
      _ = S (2 ^ m) * (p + 1) := by ring
  have hle := a_le hmemm
  have hpow : ∃ j, a p = 2 ^ j := by
    rcases a_odd hp3 hodd with h | h
    · exact h
    · rcases lt_or_eq_of_le hle with h' | h'
      · exact H _ h' h
      · exact ⟨m, h'⟩
  obtain ⟨i, hi⟩ := hpow
  have hmemi : 2 ^ i ∈ T p := by
    rw [← hi]
    exact a_mem ⟨_, hmemm⟩
  rw [two_pow_mem_iff _ hp0 hodd, hSp] at hmemi
  have hBi := S_two_pow i
  have hpBi : p ≤ S (2 ^ i) := by
    have e1 : (S (2 ^ i) + 1) * p = S (2 ^ i) * p + p := by ring
    have e2 : S (2 ^ i) * (p + 1) = S (2 ^ i) * p + S (2 ^ i) := by ring
    omega
  have h1 : 2 ^ m < 2 ^ (i + 1) := by omega
  have hmi : m < i + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h1
  have h2 : 2 ^ i ≤ 2 ^ m := by
    rw [← hi]
    exact hle
  have him : i ≤ m := (Nat.pow_le_pow_iff_right (by norm_num)).1 h2
  have : i = m := by omega
  rw [hi, this]

/-- Unconditional half of Conjecture 2: `a n = 2 ^ m` forces `n` to be at least the least
prime above `2 ^ m`. -/
theorem nextPrime_le_of_a_eq (m : ℕ) (hm : 1 ≤ m) (n : ℕ) (hn : 2 ≤ n) (h : a n = 2 ^ m) :
    nextPrimeTwoPow m ≤ n := by
  have h2m := two_le_two_pow hm
  rcases Nat.even_or_odd n with he | ho
  · have h3 := a_even (by omega) he
    have hm1 : m = 1 := by
      have h4 : 2 ^ m < 2 ^ 2 := by
        have : (2 : ℕ) ^ 2 = 4 := by norm_num
        omega
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 h4
      omega
    subst hm1
    have hn2 : n ≠ 2 := by
      rintro rfl
      have hmem : a 2 ∈ T 2 := a_mem ⟨3, three_mem (by norm_num) he⟩
      rw [h, mem_iff] at hmem
      have hS4 : S (2 ^ 1 * 2) = 7 := by decide
      omega
    have hle : nextPrimeTwoPow 1 ≤ 3 := nextPrime_le (by norm_num) (by norm_num)
    obtain ⟨t, rfl⟩ := he
    omega
  · have hn3 : 3 ≤ n := by
      obtain ⟨t, rfl⟩ := ho
      omega
    have hn0 : 0 < n := by omega
    obtain ⟨i, rfl⟩ : ∃ i, m = i + 1 := ⟨m - 1, by omega⟩
    have hlt : 2 ^ i < a n := by
      rw [h]
      exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hnot := not_mem_of_lt hlt
    rw [two_pow_mem_iff _ hn0 ho, not_le] at hnot
    have hB := S_two_pow i
    have hq : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    have hqn : Nat.minFac n ∣ n := Nat.minFac_dvd n
    generalize Nat.minFac n = q at hq hqn
    obtain ⟨r, hr⟩ := hqn
    have hrn : r ≠ n := by
      intro hrn
      have : 2 * r ≤ q * r := Nat.mul_le_mul_right r hq.two_le
      omega
    have hS : n + r ≤ S n := S_ge_add hn0 ⟨q, by rw [hr]; ring⟩ hrn
    have h1 : S (2 ^ i) * (n + r) < (S (2 ^ i) + 1) * n :=
      lt_of_le_of_lt (Nat.mul_le_mul_left _ hS) hnot
    have h2 : S (2 ^ i) * r < q * r := by
      have e1 : S (2 ^ i) * (n + r) = S (2 ^ i) * n + S (2 ^ i) * r := by ring
      have e2 : (S (2 ^ i) + 1) * n = S (2 ^ i) * n + n := by ring
      omega
    have h3 : S (2 ^ i) < q := lt_of_mul_lt_mul_right h2 (Nat.zero_le r)
    have hqodd : Odd q := by
      rcases hq.eq_two_or_odd' with h' | h'
      · exfalso
        have h2n : 2 ∣ n := ⟨r, by rw [hr, h']⟩
        exact (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 h2n)
      · exact h'
    have hne : q ≠ 2 ^ (i + 1) := by
      intro h'
      rw [h'] at hqodd
      exact (Nat.not_even_iff_odd.2 hqodd) (Nat.even_pow.2 ⟨even_two, by omega⟩)
    have hqgt : 2 ^ (i + 1) < q := by omega
    exact (nextPrime_le hqgt hq).trans (Nat.le_of_dvd hn0 ⟨r, hr⟩)

/-- Bounded form of Conjecture 2. -/
theorem conjecture_2_of_bound (m : ℕ) (hm : 1 ≤ m)
    (H : ∀ k < 2 ^ m, AlmostPerfect k → ∃ j, k = 2 ^ j) :
    IsLeast {n : ℕ | 2 ≤ n ∧ a n = 2 ^ m} (nextPrimeTwoPow m) := by
  refine ⟨⟨(nextPrime_spec m).2.two_le, a_nextPrime m hm H⟩, ?_⟩
  rintro n ⟨hn, h⟩
  exact nextPrime_le_of_a_eq m hm n hn h

/-- **A215926 Conjecture 2 follows from the almost perfect number conjecture.** -/
theorem conjecture_2_of_almostPerfect (H : ∀ k, AlmostPerfect k → ∃ j, k = 2 ^ j)
    (m : ℕ) (hm : 1 ≤ m) :
    IsLeast {n : ℕ | 2 ≤ n ∧ a n = 2 ^ m} (nextPrimeTwoPow m) :=
  conjecture_2_of_bound m hm (fun k _ hk => H k hk)

/-- Both conjectures of A215926, assuming a negative answer to the open question
`AlmostPerfectNumbers.exists_almost_perfect_not_power_of_two` of formal-conjectures. -/
theorem conjectures_of_no_exotic_almostPerfect
    (H : ¬ ∃ n : ℕ, AlmostPerfect n ∧ ¬ ∃ k : ℕ, n = 2 ^ k) :
    (∀ n : ℕ, 2 ≤ n → a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo) ∧
    (∀ m : ℕ, 1 ≤ m → IsLeast {n : ℕ | 2 ≤ n ∧ a n = 2 ^ m} (nextPrimeTwoPow m)) := by
  have H' : ∀ k, AlmostPerfect k → ∃ j, k = 2 ^ j := by
    intro k hk
    by_contra hcon
    exact H ⟨k, hk, hcon⟩
  exact ⟨conjecture_1_of_almostPerfect H', conjecture_2_of_almostPerfect H'⟩

/-! ### Unconditional small cases (checked by kernel computation) -/

set_option maxRecDepth 1000000 in
lemma no_exotic_lt_256 : ∀ k < 256, S k + 1 = 2 * k →
    k = 1 ∨ k = 2 ∨ k = 4 ∨ k = 8 ∨ k = 16 ∨ k = 32 ∨ k = 64 ∨ k = 128 := by decide

lemma almostPerfect_lt_256 (k : ℕ) (hk : k < 256) (h : AlmostPerfect k) : ∃ j, k = 2 ^ j := by
  rcases no_exotic_lt_256 k hk ((almostPerfect_iff k).1 h) with h | h | h | h | h | h | h | h
  exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩, ⟨3, h⟩, ⟨4, h⟩, ⟨5, h⟩, ⟨6, h⟩, ⟨7, h⟩]

/-- Conjecture 1 holds unconditionally for `2 ≤ n < 256`. -/
theorem conjecture_1_small (n : ℕ) (hn : 2 ≤ n) (hN : n < 256) :
    a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo :=
  conjecture_1_of_bound 255 (fun k hk => almostPerfect_lt_256 k (by omega)) n hn (by omega)

/-- Conjecture 2 holds unconditionally for `1 ≤ m ≤ 8`. -/
theorem conjecture_2_small (m : ℕ) (hm : 1 ≤ m) (hm8 : m ≤ 8) :
    IsLeast {n : ℕ | 2 ≤ n ∧ a n = 2 ^ m} (nextPrimeTwoPow m) := by
  have h8 : 2 ^ m ≤ 256 := by
    calc 2 ^ m ≤ 2 ^ 8 := Nat.pow_le_pow_right (by norm_num) hm8
      _ = 256 := by norm_num
  exact conjecture_2_of_bound m hm (fun k hk => almostPerfect_lt_256 k (by omega))

/-! ### The converse: an exotic almost perfect number refutes Conjecture 1

Let `k` be the least almost perfect number that is not a power of two, `2^j < k < 2^(j+1)`,
`c = σ(k) = 2k - 1`, `B = σ(2^j) = 2^(j+1) - 1`. We build `n` as a product of distinct primes
`≥ (c+1)^2`, adding primes one at a time until `σ(n)/n ≥ (c+1)/c` for the first time; this
happens because the sum of the reciprocals of the primes diverges. For this `n` one gets
`a n = k`. -/

lemma S_mul_coprime {m n : ℕ} (h : Nat.Coprime m n) : S (m * n) = S m * S n := by
  unfold S
  exact Nat.Coprime.sum_divisors_mul h

/-- Primes `p` with `M ≤ p < x`. -/
def F (M x : ℕ) : Finset ℕ := (Finset.range x).filter (fun p => p.Prime ∧ M ≤ p)

/-- Product of the primes `p` with `M ≤ p < x`. -/
def Nn (M x : ℕ) : ℕ := ∏ p ∈ F M x, p

/-- Product of `p + 1` over the primes `p` with `M ≤ p < x`. -/
def Ss (M x : ℕ) : ℕ := ∏ p ∈ F M x, (p + 1)

lemma mem_F {M x p : ℕ} : p ∈ F M x ↔ p < x ∧ p.Prime ∧ M ≤ p := by
  simp [F]

lemma F_zero (M : ℕ) : F M 0 = ∅ := by
  simp [F]

lemma not_mem_F (M x : ℕ) : x ∉ F M x := by
  simp [F]

lemma F_succ (M x : ℕ) :
    F M (x + 1) = if x.Prime ∧ M ≤ x then insert x (F M x) else F M x := by
  unfold F
  rw [Finset.range_add_one, Finset.filter_insert]

lemma Nn_Ss_succ_of {M x : ℕ} (h : x.Prime ∧ M ≤ x) :
    Nn M (x + 1) = x * Nn M x ∧ Ss M (x + 1) = (x + 1) * Ss M x := by
  have hF : F M (x + 1) = insert x (F M x) := by
    rw [F_succ]
    simp [h]
  unfold Nn Ss
  rw [hF, Finset.prod_insert (not_mem_F M x), Finset.prod_insert (not_mem_F M x)]
  exact ⟨rfl, rfl⟩

lemma Nn_Ss_succ_of_not {M x : ℕ} (h : ¬ (x.Prime ∧ M ≤ x)) :
    Nn M (x + 1) = Nn M x ∧ Ss M (x + 1) = Ss M x := by
  have hF : F M (x + 1) = F M x := by
    rw [F_succ]
    simp [h]
  unfold Nn Ss
  rw [hF]
  exact ⟨rfl, rfl⟩

lemma coprime_Nn {M k' : ℕ} (hk0 : 0 < k') (hk : k' < M) (x : ℕ) :
    Nat.Coprime k' (Nn M x) := by
  unfold Nn
  apply Nat.Coprime.prod_right
  intro p hp
  obtain ⟨-, hpp, hMp⟩ := mem_F.1 hp
  exact ((Nat.Prime.coprime_iff_not_dvd hpp).2
    (Nat.not_dvd_of_pos_of_lt hk0 (by omega))).symm

/-- `σ` of the product is the product of the `p + 1`. -/
lemma S_Nn (M x : ℕ) : S (Nn M x) = Ss M x := by
  induction x with
  | zero => simp [Nn, Ss, F_zero, S]
  | succ x ih =>
    by_cases h : x.Prime ∧ M ≤ x
    · obtain ⟨h1, h2⟩ := Nn_Ss_succ_of h
      have hcop : Nat.Coprime x (Nn M x) := by
        unfold Nn
        apply Nat.Coprime.prod_right
        intro p hp
        obtain ⟨hlt, hpp, -⟩ := mem_F.1 hp
        exact (Nat.coprime_primes h.1 hpp).2 (by omega)
      rw [h1, h2, S_mul_coprime hcop, S_prime h.1, ih]
    · obtain ⟨h1, h2⟩ := Nn_Ss_succ_of_not h
      rw [h1, h2, ih]

/-- `∏ (1 + 1/p) ≥ 1 + ∑ 1/p`, cleared of denominators. -/
lemma prod_ge (G : Finset ℕ) (hG : ∀ p ∈ G, 0 < p) :
    (1 + ∑ p ∈ G, (1 / p : ℝ)) * ∏ p ∈ G, (p : ℝ) ≤ ∏ p ∈ G, ((p : ℝ) + 1) := by
  classical
  induction G using Finset.induction_on with
  | empty => simp
  | insert q G hq ih =>
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hG q (Finset.mem_insert_self q G)
    have ih' := ih (fun p hp => hG p (Finset.mem_insert_of_mem hp))
    rw [Finset.sum_insert hq, Finset.prod_insert hq, Finset.prod_insert hq]
    have hsum : 0 ≤ ∑ p ∈ G, (1 / p : ℝ) := Finset.sum_nonneg (fun p _ => by positivity)
    have hprod : 0 ≤ ∏ p ∈ G, (p : ℝ) := Finset.prod_nonneg (fun p _ => by positivity)
    have e : (1 + (1 / (q : ℝ) + ∑ p ∈ G, (1 / p : ℝ))) * ((q : ℝ) * ∏ p ∈ G, (p : ℝ))
        = ((q : ℝ) * (1 + ∑ p ∈ G, (1 / p : ℝ)) + 1) * ∏ p ∈ G, (p : ℝ) := by
      field_simp
      ring
    rw [e]
    calc ((q : ℝ) * (1 + ∑ p ∈ G, (1 / p : ℝ)) + 1) * ∏ p ∈ G, (p : ℝ)
        ≤ ((q : ℝ) + 1) * ((1 + ∑ p ∈ G, (1 / p : ℝ)) * ∏ p ∈ G, (p : ℝ)) := by
          nlinarith [mul_nonneg hsum hprod]
      _ ≤ ((q : ℝ) + 1) * ∏ p ∈ G, ((p : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left ih' (by positivity)

/-- Divergence of `∑ 1/p`: far enough out, `σ(N)/N ≥ 3/2`. -/
lemma exists_large (M : ℕ) : ∃ x, 3 * Nn M x ≤ 2 * Ss M x := by
  refine ⟨4 ^ (M.primesBelow.card + 1) + 1, ?_⟩
  have hset : (4 ^ (M.primesBelow.card + 1)).succ.primesBelow \ M.primesBelow
      = F M (4 ^ (M.primesBelow.card + 1) + 1) := by
    ext p
    simp only [Finset.mem_sdiff, Nat.mem_primesBelow, mem_F, Nat.succ_eq_add_one]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, by by_contra h; exact h3 ⟨by omega, h2⟩⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, fun h => by omega⟩
  have h1 := one_half_le_sum_primes_ge_one_div M
  rw [hset] at h1
  have h2 := prod_ge (F M (4 ^ (M.primesBelow.card + 1) + 1))
    (fun p hp => (mem_F.1 hp).2.1.pos)
  have h3 : (0 : ℝ) ≤ ∏ p ∈ F M (4 ^ (M.primesBelow.card + 1) + 1), (p : ℝ) :=
    Finset.prod_nonneg (fun p _ => by positivity)
  have h4 : (3 : ℝ) * ∏ p ∈ F M (4 ^ (M.primesBelow.card + 1) + 1), (p : ℝ)
      ≤ 2 * ∏ p ∈ F M (4 ^ (M.primesBelow.card + 1) + 1), ((p : ℝ) + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.2 h1) h3]
  have h5 : ((3 * Nn M (4 ^ (M.primesBelow.card + 1) + 1) : ℕ) : ℝ)
      ≤ ((2 * Ss M (4 ^ (M.primesBelow.card + 1) + 1) : ℕ) : ℝ) := by
    unfold Nn Ss
    push_cast
    exact h4
  exact Nat.cast_le.1 h5

/-- Adding one large prime cannot jump over the window. -/
lemma step_arith {c B s N p : ℕ} (h : c * s < (c + 1) * N) (hB : B + 2 ≤ c) (hB0 : 0 < B)
    (hp : B * (c + 1) ≤ p) : B * (s * (p + 1)) < (B + 1) * (N * p) := by
  have hc : 0 < c := by omega
  have h1 : (c + 1) * (B * (p + 1)) ≤ c * ((B + 1) * p) := by
    have h2 : (B + 2) * p ≤ c * p := Nat.mul_le_mul_right p hB
    nlinarith
  apply Nat.lt_of_mul_lt_mul_left (a := c)
  calc c * (B * (s * (p + 1))) = (c * s) * (B * (p + 1)) := by ring
    _ < ((c + 1) * N) * (B * (p + 1)) := mul_lt_mul_of_pos_right h (by positivity)
    _ = N * ((c + 1) * (B * (p + 1))) := by ring
    _ ≤ N * (c * ((B + 1) * p)) := Nat.mul_le_mul_left N h1
    _ = c * ((B + 1) * (N * p)) := by ring

lemma ap_arith {c B s n : ℕ} (hn : 0 < n) (h1 : (c + 1) * n ≤ c * s)
    (h2 : B * s < (B + 1) * n) (hcB : c ≤ B) : False := by
  have e1 : (c + 1) * n = c * n + n := by ring
  have hsn : n ≤ s := by
    by_contra h
    have : c * s ≤ c * n := Nat.mul_le_mul_left c (by omega)
    omega
  obtain ⟨D, rfl⟩ : ∃ D, s = n + D := ⟨s - n, by omega⟩
  have e2 : c * (n + D) = c * n + c * D := by ring
  have e3 : B * (n + D) = B * n + B * D := by ring
  have e4 : (B + 1) * n = B * n + n := by ring
  have : c * D ≤ B * D := Nat.mul_le_mul_right D hcB
  omega

/-- If `k` is the least almost perfect number that is not a power of two, then `k` is a value
of the sequence. -/
theorem exists_a_eq_of_exotic {k : ℕ} (hk : AlmostPerfect k) (hnp : ¬ ∃ j, k = 2 ^ j)
    (hmin : ∀ k' < k, AlmostPerfect k' → ∃ j, k' = 2 ^ j) :
    ∃ n, 2 ≤ n ∧ a n = k := by
  rw [almostPerfect_iff] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp [S] at hk
  obtain ⟨j, hj3, hj2⟩ : ∃ j, 2 ^ j < k ∧ k < 2 ^ (j + 1) :=
    ⟨Nat.log 2 k, lt_of_le_of_ne (Nat.pow_log_le_self 2 hk0) (fun h => hnp ⟨_, h.symm⟩),
      Nat.lt_pow_succ_log_self (by norm_num) k⟩
  have hB := S_two_pow j
  obtain ⟨c, hc⟩ : ∃ c, c = S k := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = S (2 ^ j) := ⟨_, rfl⟩
  rw [← hc] at hk
  rw [← hBdef] at hB
  have e : 2 ^ (j + 1) = 2 * 2 ^ j := by ring
  have h2j : 0 < 2 ^ j := by positivity
  have hkB : k ≤ B := by omega
  have hBc : B + 2 ≤ c := by omega
  have hB0 : 0 < B := by omega
  obtain ⟨M, hM⟩ : ∃ M, M = (c + 1) * (c + 1) := ⟨_, rfl⟩
  have hcM : c + 1 ≤ M := by
    rw [hM]
    exact Nat.le_mul_of_pos_left (c + 1) (by omega)
  have hkM : k < M := by omega
  -- the first time the ratio reaches `(c+1)/c`
  have hex : ∃ x, ¬ (c * Ss M x < (c + 1) * Nn M x) := by
    obtain ⟨x, hx⟩ := exists_large M
    refine ⟨x, fun h => ?_⟩
    have h1 : c * (3 * Nn M x) ≤ c * (2 * Ss M x) := Nat.mul_le_mul_left c hx
    have h2 : 3 * Nn M x ≤ c * Nn M x := Nat.mul_le_mul_right _ (by omega)
    have e1 : c * (3 * Nn M x) = 3 * (c * Nn M x) := by ring
    have e2 : c * (2 * Ss M x) = 2 * (c * Ss M x) := by ring
    have e3 : (c + 1) * Nn M x = c * Nn M x + Nn M x := by ring
    omega
  classical
  have hP0 : c * Ss M 0 < (c + 1) * Nn M 0 := by
    simp [Nn, Ss, F_zero]
  have hspec := Nat.find_spec hex
  have hne0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hspec
    exact hspec hP0
  obtain ⟨y, hy⟩ : ∃ y, Nat.find hex = y + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hPy : c * Ss M y < (c + 1) * Nn M y :=
    not_not.1 (Nat.find_min hex (m := y) (by omega))
  rw [hy] at hspec
  have hprime : y.Prime ∧ M ≤ y := by
    by_contra h
    obtain ⟨h1, h2⟩ := Nn_Ss_succ_of_not h
    rw [h1, h2] at hspec
    exact hspec hPy
  obtain ⟨hN, hS⟩ := Nn_Ss_succ_of hprime
  obtain ⟨n, hn⟩ : ∃ n, n = Nn M (y + 1) := ⟨_, rfl⟩
  have hSn : S n = Ss M (y + 1) := by
    rw [hn]
    exact S_Nn M (y + 1)
  have h_i : (c + 1) * n ≤ c * S n := by
    rw [hSn, hn]
    exact not_lt.1 hspec
  have h_ii : B * S n < (B + 1) * n := by
    rw [hSn, hn, hS, hN]
    have hpy : B * (c + 1) ≤ y := by
      calc B * (c + 1) ≤ (c + 1) * (c + 1) := Nat.mul_le_mul_right _ (by omega)
        _ = M := hM.symm
        _ ≤ y := hprime.2
    have h := step_arith hPy hBc hB0 hpy
    have e1 : (y + 1) * Ss M y = Ss M y * (y + 1) := by ring
    have e2 : y * Nn M y = Nn M y * y := by ring
    rw [e1, e2]
    exact h
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at h_ii
      simp at h_ii
    · exact h0
  have hn1 : n ≠ 1 := by
    intro h1
    rw [h1] at h_i
    have hS1 : S 1 = 1 := by decide
    rw [hS1] at h_i
    omega
  refine ⟨n, by omega, ?_⟩
  have hcop : ∀ k', 0 < k' → k' ≤ k → S (k' * n) = S k' * S n := by
    intro k' h0 hle
    rw [hn]
    exact S_mul_coprime (coprime_Nn h0 (by omega) (y + 1))
  have hkmem : k ∈ T n := by
    rw [mem_iff, hcop k (by omega) le_rfl, ← hc]
    refine ⟨by omega, Nat.mul_pos (by omega) hn0, ?_⟩
    calc 2 * (k * n) = (2 * k) * n := by ring
      _ = (c + 1) * n := by rw [← hk]
      _ ≤ c * S n := h_i
  have hnot : ∀ k' < k, k' ∉ T n := by
    intro k' hlt hmem
    rw [mem_iff] at hmem
    obtain ⟨hdef, hpos, hnd⟩ := hmem
    have hk'0 : 0 < k' := by
      rcases Nat.eq_zero_or_pos k' with h0 | h0
      · rw [h0] at hpos
        simp at hpos
      · exact h0
    rw [hcop k' hk'0 hlt.le] at hnd
    by_cases hap : S k' + 1 = 2 * k'
    · obtain ⟨i, rfl⟩ := hmin k' hlt ((almostPerfect_iff k').2 hap)
      have hi := S_two_pow i
      have hij : i < j + 1 := (Nat.pow_lt_pow_iff_right (by norm_num)).1 (hlt.trans hj2)
      have hpow : 2 ^ (i + 1) ≤ 2 ^ (j + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hcB : S (2 ^ i) ≤ B := by omega
      refine ap_arith hn0 (c := S (2 ^ i)) ?_ h_ii hcB
      calc (S (2 ^ i) + 1) * n = 2 * (2 ^ i * n) := by rw [hap]; ring
        _ ≤ S (2 ^ i) * S n := hnd
    · exact arith_key hn0 (c := S k') (by omega) hnd h_ii (by omega)
  have hle := a_le hkmem
  have hmem := a_mem ⟨k, hkmem⟩
  by_contra hne
  exact hnot (a n) (lt_of_le_of_ne hle hne) hmem

/-- **Conjecture 1 implies the almost perfect number conjecture.** -/
theorem almostPerfect_of_conjecture_1
    (H : ∀ n : ℕ, 2 ≤ n → a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo) :
    ∀ k, AlmostPerfect k → ∃ j, k = 2 ^ j := by
  by_contra hcon
  have hex : ∃ k, AlmostPerfect k ∧ ¬ ∃ j, k = 2 ^ j := by
    by_contra h
    apply hcon
    intro k hk
    by_contra h'
    exact h ⟨k, hk, h'⟩
  classical
  obtain ⟨hk, hnp⟩ := Nat.find_spec hex
  have hmin : ∀ k' < Nat.find hex, AlmostPerfect k' → ∃ j, k' = 2 ^ j := by
    intro k' hlt hk'
    by_contra h'
    exact Nat.find_min hex hlt ⟨hk', h'⟩
  obtain ⟨n, hn, han⟩ := exists_a_eq_of_exotic hk hnp hmin
  rcases H n hn with h | h | ⟨j, hj⟩
  · exact hnp ⟨0, by rw [← han, h]; norm_num⟩
  · rw [← han, h, almostPerfect_iff] at hk
    have hS3 : S 3 = 4 := by decide
    omega
  · exact hnp ⟨j, by rw [← han]; exact hj⟩

/-- **A215926 Conjecture 1 is equivalent to the almost perfect number conjecture**
(a negative answer to `AlmostPerfectNumbers.exists_almost_perfect_not_power_of_two`). -/
theorem conjecture_1_iff_almostPerfect :
    (∀ n : ℕ, 2 ≤ n → a n = 1 ∨ a n = 3 ∨ (a n).isPowerOfTwo) ↔
      ¬ ∃ n : ℕ, AlmostPerfect n ∧ ¬ ∃ k : ℕ, n = 2 ^ k := by
  constructor
  · rintro H ⟨k, hk, hnp⟩
    exact hnp (almostPerfect_of_conjecture_1 H k hk)
  · intro H
    exact (conjectures_of_no_exotic_almostPerfect H).1

end OeisA215926

#print axioms OeisA215926.conjecture_1_unconditional
#print axioms OeisA215926.nextPrime_le_of_a_eq
#print axioms OeisA215926.conjectures_of_no_exotic_almostPerfect
#print axioms OeisA215926.conjecture_1_small
#print axioms OeisA215926.conjecture_2_small
#print axioms OeisA215926.conjecture_1_iff_almostPerfect

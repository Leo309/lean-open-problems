/-
OEIS A017666 and practical numbers: Coleman's conjecture is equivalent to the
nonexistence of odd multiply perfect numbers.

`a(n)` (OEIS A017666) is the denominator of `σ(n)/n` in lowest terms, that is
`n / gcd(n, σ(n))`. A positive integer is *practical* (OEIS A005153) if every `m ≤ n` is a
sum of distinct divisors of `n`. The OEIS entry A017666 records (J. Coleman, 2014):

  Conjecture: if `a(n)` is practical, then `n` is practical.

It is stated formally in google-deepmind/formal-conjectures
(`FormalConjectures/OEIS/17666.lean`, theorem `OeisA17666.conjecture`, marked open).
Coleman already observed that an odd `n` with `a(n)` practical must be multiply perfect, so
the conjecture implies that no odd multiply perfect number exists.

This file proves, with no `sorry`:

* `coleman_iff_noOddMultiperfect`: the conjecture is *equivalent* to the statement that there
  is no odd `N > 1` with `N ∣ σ(N)` (no odd multiply perfect number, in particular no odd
  perfect number);
* `counterexample_structure`: any counterexample `n` has a unitary divisor `N > 1` that is an
  odd multiply perfect number;
* `coleman_bounded`: the conjecture holds for all `n ≤ X` iff there is no odd multiply perfect
  number `N` with `1 < N ≤ X`;
* `coleman_dyadic_iff_noOddMultiperfect`: the special case singled out in the OEIS comment
  (`a(n)` a power of 2 implies `n` practical) is equivalent to the same statement;
* `multiperfectPractical_iff_noOddMultiperfect`: Coleman's companion conjecture at OEIS
  A007691 (every multiply perfect number is practical) is equivalent to the same statement;
* on the way, the sufficiency half of Stewart's structure theorem for practical numbers
  (`SC_of_stewart`): if every prime `p ∣ n` satisfies `p ≤ 1 + σ(part of n with primes < p)`,
  then every `x ≤ σ(n)` is a sum of distinct divisors of `n`.

The definitions `a`, `IsPractical`, `A5153` agree with `OeisA17666.a`, `Nat.IsPractical`
and `OeisA5153.A` of formal-conjectures (with `subsetSums` unfolded).

Checked with Lean 4.36.0 and Mathlib v4.36.0. Every theorem depends only on the axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

open Finset

namespace A017666

/-- Sum of the divisors of `n`. -/
def sig (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- `x` is a sum of distinct divisors of `n`. -/
def IsSum (n x : ℕ) : Prop :=
  ∃ B : Finset ℕ, (↑B : Set ℕ) ⊆ ↑n.divisors ∧ x = ∑ i ∈ B, i

/-- Practical: every `m ≤ n` is a sum of distinct divisors of `n`. -/
def IsPractical (n : ℕ) : Prop := ∀ m, m ≤ n → IsSum n m

/-- Membership in OEIS A005153. -/
def A5153 (n : ℕ) : Prop := 0 < n ∧ IsPractical n

/-- OEIS A017666: denominator of `σ(n)/n`. -/
def a (n : ℕ) : ℕ := if n = 0 then 1 else n / Nat.gcd n (∑ d ∈ n.divisors, d)

/-- Coleman's conjecture. -/
def ColemanConjecture : Prop := ∀ n : ℕ, 0 < n → A5153 (a n) → A5153 n

/-- No odd multiply perfect number other than 1. -/
def NoOddMultiperfect : Prop := ∀ N : ℕ, Odd N → N ∣ ∑ d ∈ N.divisors, d → N = 1

/-- every `x ≤ σ(n)` is a sum of distinct divisors -/
def SC (n : ℕ) : Prop := ∀ x, x ≤ sig n → IsSum n x

open Classical in
/-- Sum of the divisors of `n` all of whose prime factors are `< p`. -/
noncomputable def slo (n p : ℕ) : ℕ :=
  ∑ e ∈ n.divisors.filter (fun e => ∀ r : ℕ, r.Prime → r ∣ e → r < p), e

lemma sig_pos {n : ℕ} (hn : 0 < n) : 0 < sig n := by
  unfold sig
  have : 1 ∈ n.divisors := by simp; omega
  calc 0 < 1 := one_pos
    _ ≤ ∑ d ∈ n.divisors, d := Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) this

lemma le_sig {n : ℕ} (hn : 0 < n) : n ≤ sig n := by
  unfold sig
  have : n ∈ n.divisors := by simp; omega
  exact Finset.single_le_sum (f := fun d => d) (fun _ _ => Nat.zero_le _) this

lemma SC.practical {n : ℕ} (hn : 0 < n) (h : SC n) : IsPractical n :=
  fun m hm => h m (hm.trans (le_sig hn))

lemma sig_mul {m n : ℕ} (h : m.Coprime n) : sig (m * n) = sig m * sig n := by
  unfold sig; exact Nat.Coprime.sum_divisors_mul h

lemma sig_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : sig (p ^ k) = ∑ j ∈ range (k + 1), p ^ j := by
  unfold sig; exact Nat.sum_divisors_prime_pow hp

lemma sig_le_of_dvd {m n : ℕ} (hn : 0 < n) (h : m ∣ n) : sig m ≤ sig n := by
  unfold sig
  exact Finset.sum_le_sum_of_subset (Nat.divisors_subset_of_dvd (by omega) h)

/-- Key step: adjoining a prime power. -/
lemma SC_mul_prime_pow {m p : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hsc : SC m) (hle : p ≤ sig m + 1) (k : ℕ) :
    SC (m * p ^ k) ∧ p ^ (k + 1) ≤ sig (m * p ^ k) + 1 := by
  have hcop : ∀ j, m.Coprime (p ^ j) := fun j =>
    Nat.Coprime.pow_right j ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm
  induction k with
  | zero => simpa using ⟨hsc, hle⟩
  | succ k ih =>
    obtain ⟨ihsc, ihle⟩ := ih
    have hsig : sig (m * p ^ (k + 1)) = sig (m * p ^ k) + p ^ (k + 1) * sig m := by
      rw [sig_mul (hcop _), sig_mul (hcop _), sig_prime_pow hp, sig_prime_pow hp,
        Finset.sum_range_succ _ (k + 1)]
      ring
    have hpp : 0 < p ^ (k + 1) := pow_pos hp.pos _
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [hsig] at hx
      -- choose the multiple of p^(k+1)
      obtain ⟨t, ht, hlo, hhi⟩ : ∃ t, t ≤ sig m ∧ p ^ (k + 1) * t ≤ x ∧
          x - p ^ (k + 1) * t ≤ sig (m * p ^ k) := by
        generalize hPdef : p ^ (k + 1) = P at *
        obtain ⟨q, r, hqr, hr⟩ : ∃ q r, P * q + r = x ∧ r < P :=
          ⟨x / P, x % P, Nat.div_add_mod x P, Nat.mod_lt x hpp⟩
        by_cases hc : q ≤ sig m
        · exact ⟨q, hc, by omega, by omega⟩
        · have h5 : P * sig m ≤ P * q := Nat.mul_le_mul_left _ (by omega)
          exact ⟨sig m, le_refl _, by omega, by omega⟩
      obtain ⟨B1, hB1, hs1⟩ := ihsc _ hhi
      obtain ⟨B2, hB2, hs2⟩ := hsc _ ht
      refine ⟨B1 ∪ B2.image (fun e => p ^ (k + 1) * e), ?_, ?_⟩
      · intro e he
        simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Finset.mem_coe,
          Set.mem_image] at he
        simp only [Finset.mem_coe, Nat.mem_divisors]
        rcases he with he | ⟨f, hf, rfl⟩
        · have := hB1 he
          simp only [Finset.mem_coe, Nat.mem_divisors] at this
          refine ⟨this.1.trans (Nat.mul_dvd_mul_left m (pow_dvd_pow p (Nat.le_succ k))), ?_⟩
          exact (Nat.mul_pos hm hpp).ne'
        · have := hB2 hf
          simp only [Finset.mem_coe, Nat.mem_divisors] at this
          refine ⟨?_, (Nat.mul_pos hm hpp).ne'⟩
          rw [mul_comm m]
          exact Nat.mul_dvd_mul_left _ this.1
      · have hdisj : Disjoint B1 (B2.image (fun e => p ^ (k + 1) * e)) := by
          rw [Finset.disjoint_left]
          intro e he1 he2
          obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 he2
          have := hB1 he1
          simp only [Finset.mem_coe, Nat.mem_divisors] at this
          have h3 : p ^ (k + 1) ∣ m * p ^ k := (Dvd.intro _ rfl).trans this.1
          have h4 : p ^ (k + 1) ∣ p ^ k := (Nat.Coprime.dvd_mul_left (hcop (k + 1)).symm).1 h3
          have := Nat.le_of_dvd (pow_pos hp.pos _) h4
          have := Nat.pow_lt_pow_right hp.one_lt (show k < k + 1 by omega)
          omega
        have hinj : ∀ u ∈ B2, ∀ v ∈ B2, p ^ (k + 1) * u = p ^ (k + 1) * v → u = v :=
          fun u _ v _ huv => Nat.eq_of_mul_eq_mul_left hpp huv
        rw [Finset.sum_union hdisj, Finset.sum_image hinj, ← Finset.mul_sum, ← hs1, ← hs2]
        omega
    · rw [hsig]
      have h1 : p ^ (k + 1 + 1) = p ^ (k + 1) * p := pow_succ _ _
      have h2 : p ^ (k + 1) * p ≤ p ^ (k + 1) * (sig m + 1) := Nat.mul_le_mul_left _ hle
      rw [h1]
      have : p ^ (k + 1) * (sig m + 1) = p ^ (k + 1) * sig m + p ^ (k + 1) := by ring
      omega

lemma SC_one : SC 1 := by
  intro x hx
  have : sig 1 = 1 := by simp [sig]
  rw [this] at hx
  interval_cases x
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by simp, by simp⟩

/-- Sufficiency half of Stewart's criterion. -/
theorem SC_of_stewart : ∀ n : ℕ, 0 < n →
    (∀ p : ℕ, p.Prime → p ∣ n → p ≤ 1 + slo n p) → SC n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn H
  by_cases h1 : n = 1
  · subst h1; exact SC_one
  -- largest prime factor
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by omega)
  set P := n.primeFactors.max' hne with hP
  have hPmem : P ∈ n.primeFactors := Finset.max'_mem _ _
  have hPp : P.Prime := Nat.prime_of_mem_primeFactors hPmem
  have hPn : P ∣ n := Nat.dvd_of_mem_primeFactors hPmem
  have hmax : ∀ r : ℕ, r.Prime → r ∣ n → r ≤ P := fun r hr hrn =>
    Finset.le_max' _ _ (Nat.mem_primeFactors.2 ⟨hr, hrn, by omega⟩)
  set k := n.factorization P with hk
  set n' := n / P ^ k with hn'
  have hdec : P ^ k * n' = n := Nat.ordProj_mul_ordCompl_eq_self n P
  have hPn' : ¬ P ∣ n' := Nat.not_dvd_ordCompl hPp (by omega)
  have hn'pos : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h | h
    · rw [h] at hdec; omega
    · exact h
  have hkpos : 0 < k := hPp.factorization_pos_of_dvd (by omega) hPn
  have hn'lt : n' < n := by
    have : 2 ≤ P ^ k := by
      calc 2 ≤ P := hPp.two_le
        _ = P ^ 1 := (pow_one P).symm
        _ ≤ P ^ k := Nat.pow_le_pow_right hPp.pos hkpos
    nlinarith
  have hn'n : n' ∣ n := Dvd.intro_left _ hdec
  -- divisors of n with all prime factors < q ≤ P divide n'
  have hsmooth : ∀ q e : ℕ, q ≤ P → e ∣ n → (∀ r : ℕ, r.Prime → r ∣ e → r < q) → e ∣ n' := by
    intro q e hq hen hsm
    have hcop : e.Coprime (P ^ k) := by
      apply Nat.Coprime.pow_right
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hPp]
      intro hPe
      have := hsm P hPp hPe
      omega
    rw [← hdec] at hen
    exact (Nat.Coprime.dvd_mul_left hcop).1 hen
  have hSCn' : SC n' := by
    apply ih n' hn'lt hn'pos
    intro q hq hqn'
    have hqn : q ∣ n := hqn'.trans hn'n
    have hqP : q ≤ P := hmax q hq hqn
    refine (H q hq hqn).trans ?_
    apply Nat.add_le_add_left
    unfold slo
    apply Finset.sum_le_sum_of_subset
    intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he ⊢
    exact ⟨⟨hsmooth q e hqP he.1.1 he.2, by omega⟩, he.2⟩
  have hPle : P ≤ sig n' + 1 := by
    refine (H P hPp hPn).trans ?_
    rw [add_comm]
    apply Nat.add_le_add_right
    unfold slo sig
    apply Finset.sum_le_sum_of_subset
    intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he ⊢
    exact ⟨hsmooth P e (le_refl _) he.1.1 he.2, by omega⟩
  have := (SC_mul_prime_pow hn'pos hPp hPn' hSCn' hPle k).1
  rwa [mul_comm, hdec] at this

/-- Necessity half of Stewart's criterion (in the form we need). -/
lemma practical_prime_le {d q : ℕ} (hd : 0 < d) (hpr : IsPractical d) (hq : q.Prime)
    (hqd : q ∣ d) : q ≤ 1 + ∑ e ∈ d.divisors.filter (· < q), e := by
  have hle : q - 1 ≤ d := by have := Nat.le_of_dvd hd hqd; omega
  obtain ⟨B, hB, hs⟩ := hpr _ hle
  have hsub : B ⊆ d.divisors.filter (· < q) := by
    intro e he
    have h1 : e ≤ ∑ i ∈ B, i := Finset.single_le_sum (f := fun i => i) (fun _ _ => Nat.zero_le _) he
    have h2 := hB he
    simp only [Finset.mem_coe] at h2
    rw [Finset.mem_filter]
    have := hq.pos
    exact ⟨h2, by omega⟩
  have := Finset.sum_le_sum_of_subset (f := fun i => i) hsub
  omega

/-- Splitting `n` into its part with primes `< p` and its part with primes `≥ p`. -/
lemma exists_split (p : ℕ) : ∀ n : ℕ, 0 < n → ∃ m N : ℕ, n = m * N ∧ m.Coprime N ∧
    (∀ r : ℕ, r.Prime → r ∣ m → r < p) ∧ (∀ r : ℕ, r.Prime → r ∣ N → p ≤ r) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn
  by_cases h1 : n = 1
  · subst h1
    refine ⟨1, 1, rfl, Nat.coprime_one_left 1, ?_, ?_⟩ <;>
    · intro r hr hr1
      exact absurd (Nat.dvd_one.1 hr1) hr.ne_one
  set q := n.minFac with hq
  have hqp : q.Prime := Nat.minFac_prime h1
  have hqn : q ∣ n := Nat.minFac_dvd n
  set k := n.factorization q
  set n' := n / q ^ k
  have hdec : q ^ k * n' = n := Nat.ordProj_mul_ordCompl_eq_self n q
  have hqn' : ¬ q ∣ n' := Nat.not_dvd_ordCompl hqp (by omega)
  have hn'pos : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h | h
    · rw [h] at hdec; omega
    · exact h
  have hkpos : 0 < k := hqp.factorization_pos_of_dvd (by omega) hqn
  have hn'lt : n' < n := by
    have : 2 ≤ q ^ k := by
      calc 2 ≤ q := hqp.two_le
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ k := Nat.pow_le_pow_right hqp.pos hkpos
    nlinarith
  obtain ⟨m, N, hmN, hcop, hm, hN⟩ := ih n' hn'lt hn'pos
  have hqm : ¬ q ∣ m := fun h => hqn' (hmN ▸ Dvd.dvd.mul_right h N)
  have hqN : ¬ q ∣ N := fun h => hqn' (hmN ▸ Dvd.dvd.mul_left h m)
  have hcm : (q ^ k).Coprime m :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hqp).2 hqm)
  have hcN : (q ^ k).Coprime N :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hqp).2 hqN)
  by_cases hqlt : q < p
  · refine ⟨q ^ k * m, N, by rw [← hdec, hmN]; ring, Nat.Coprime.mul_left hcN hcop, ?_, hN⟩
    intro r hr hrd
    rcases (Nat.Prime.dvd_mul hr).1 hrd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hr hqp).1 (hr.dvd_of_dvd_pow h)
      omega
    · exact hm r hr h
  · refine ⟨m, q ^ k * N, by rw [← hdec, hmN]; ring, Nat.Coprime.mul_right hcm.symm hcop, hm, ?_⟩
    intro r hr hrd
    rcases (Nat.Prime.dvd_mul hr).1 hrd with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hr hqp).1 (hr.dvd_of_dvd_pow h)
      omega
    · exact hN r hr h

/-- Structure of a counterexample: it has an odd multiply perfect unitary divisor `N > 1`. -/
theorem counterexample_structure {n : ℕ} (hn : 0 < n) (ha : A5153 (a n)) (hnp : ¬ A5153 n) :
    ∃ N : ℕ, N ∣ n ∧ N.Coprime (n / N) ∧ N ≠ 1 ∧ Odd N ∧ N ∣ ∑ d ∈ N.divisors, d := by
  have hnp' : ¬ IsPractical n := fun h => hnp ⟨hn, h⟩
  -- a violating prime
  obtain ⟨p, hp, hpn, hviol⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ 1 + slo n p < p := by
    by_contra hcon
    push Not at hcon
    exact hnp' (SC.practical hn (SC_of_stewart n hn hcon))
  set g := Nat.gcd n (∑ d ∈ n.divisors, d) with hg
  have had : a n = n / g := by unfold a; rw [if_neg (by omega : ¬ _ = 0)]
  set d := a n with hd
  have hgn : g ∣ n := Nat.gcd_dvd_left _ _
  have hdg : d * g = n := by rw [had]; exact Nat.div_mul_cancel hgn
  have hdn : d ∣ n := Dvd.intro _ hdg
  -- no prime ≥ p divides d
  have hstep1 : ∀ q : ℕ, q.Prime → q ∣ d → q < p := by
    by_contra hcon
    push Not at hcon
    have hex : ∃ q : ℕ, q.Prime ∧ q ∣ d ∧ p ≤ q := hcon
    classical
    obtain ⟨q0, ⟨hq0p, hq0d, hq0le⟩, hmin⟩ : ∃ q0 : ℕ, (q0.Prime ∧ q0 ∣ d ∧ p ≤ q0) ∧
        ∀ r : ℕ, (r.Prime ∧ r ∣ d ∧ p ≤ r) → q0 ≤ r :=
      ⟨Nat.find hex, Nat.find_spec hex, fun r hr => Nat.find_min' hex hr⟩
    have hbound := practical_prime_le ha.1 ha.2 hq0p hq0d
    have hsub : ∑ e ∈ d.divisors.filter (· < q0), e ≤ slo n p := by
      unfold slo
      apply Finset.sum_le_sum_of_subset
      intro e he
      simp only [Finset.mem_filter, Nat.mem_divisors] at he ⊢
      refine ⟨⟨he.1.1.trans hdn, by omega⟩, ?_⟩
      intro r hr hre
      by_contra hrp
      push Not at hrp
      have hrle : r ≤ e := Nat.le_of_dvd (Nat.pos_of_ne_zero (fun h0 => by
        rw [h0] at he; exact he.1.2 (Nat.eq_zero_of_zero_dvd he.1.1))) hre
      have := hmin r ⟨hr, hre.trans he.1.1, hrp⟩
      omega
    omega
  obtain ⟨m, N, hmN, hcop, hm, hN⟩ := exists_split p n hn
  have hmpos : 0 < m := Nat.pos_of_ne_zero (fun h => by rw [h] at hmN; omega)
  have hNpos : 0 < N := Nat.pos_of_ne_zero (fun h => by rw [h] at hmN; omega)
  have hpN : p ∣ N := by
    rw [hmN] at hpn
    rcases (Nat.Prime.dvd_mul hp).1 hpn with h | h
    · exact absurd (hm p hp h) (lt_irrefl _)
    · exact h
  have hNn : N ∣ n := Dvd.intro_left _ hmN.symm
  have hNd : N.Coprime d := Nat.coprime_of_dvd (fun r hr hrN hrd => by
    have := hN r hr hrN; have := hstep1 r hr hrd; omega)
  have hNg : N ∣ g := by
    have : N ∣ d * g := hdg ▸ hNn
    exact (Nat.Coprime.dvd_mul_left hNd).1 this
  have hNsig : N ∣ sig m * sig N := by
    rw [← sig_mul hcop, ← hmN]
    exact hNg.trans (Nat.gcd_dvd_right _ _)
  have hsm : sig m ≤ slo n p := by
    unfold slo sig
    apply Finset.sum_le_sum_of_subset
    intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he ⊢
    exact ⟨⟨he.1.trans (Dvd.intro _ hmN.symm), by omega⟩, fun r hr hre => hm r hr (hre.trans he.1)⟩
  have hNsm : N.Coprime (sig m) := Nat.coprime_of_dvd (fun r hr hrN hrs => by
    have := hN r hr hrN
    have := Nat.le_of_dvd (sig_pos hmpos) hrs
    omega)
  refine ⟨N, hNn, ?_, ?_, ?_, ?_⟩
  · rw [hmN, Nat.mul_div_cancel _ hNpos]; exact hcop.symm
  · intro h; rw [h] at hpN; exact hp.ne_one (Nat.dvd_one.1 hpN)
  · rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    have := hN 2 Nat.prime_two h2
    have := sig_pos hmpos
    omega
  · exact (Nat.Coprime.dvd_mul_left hNsm).1 hNsig

lemma practical_one : A5153 1 := by
  refine ⟨one_pos, fun m hm => ?_⟩
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by simp, by simp⟩

/-- An odd number greater than 1 is not practical. -/
lemma not_practical_of_odd {N : ℕ} (hodd : Odd N) (h1 : N ≠ 1) : ¬ A5153 N := by
  rintro ⟨hpos, hpr⟩
  have h3 : 2 ≤ N := by omega
  obtain ⟨B, hB, hs⟩ := hpr 2 h3
  have hsub : B ⊆ {1} := by
    intro e he
    have h1 : e ≤ ∑ i ∈ B, i := Finset.single_le_sum (f := fun i => i) (fun _ _ => Nat.zero_le _) he
    have h2 := hB he
    simp only [Finset.mem_coe, Nat.mem_divisors] at h2
    have hoe : Odd e := Odd.of_dvd_nat hodd h2.1
    rw [Finset.mem_singleton]
    rcases hoe with ⟨t, ht⟩
    omega
  have := Finset.sum_le_sum_of_subset (f := fun i => i) hsub
  simp at this
  omega

/-- **Main theorem.** Coleman's conjecture on A017666 is equivalent to the nonexistence of
odd multiply perfect numbers greater than 1. -/
theorem coleman_iff_noOddMultiperfect : ColemanConjecture ↔ NoOddMultiperfect := by
  constructor
  · intro hC N hodd hdiv
    by_contra h1
    have hNpos : 0 < N := hodd.pos
    have haN : a N = 1 := by
      unfold a
      rw [if_neg (by omega : ¬ _ = 0), Nat.gcd_eq_left hdiv, Nat.div_self hNpos]
    exact not_practical_of_odd hodd h1 (hC N hNpos (haN ▸ practical_one))
  · intro hno n hn ha
    by_contra hnp
    obtain ⟨N, -, -, hN1, hodd, hdiv⟩ := counterexample_structure hn ha hnp
    exact hN1 (hno N hodd hdiv)

/-- Bounded version: the conjecture holds up to `X` iff there is no odd multiply perfect
number in `(1, X]`. -/
theorem coleman_bounded (X : ℕ) :
    (∀ n : ℕ, 0 < n → n ≤ X → A5153 (a n) → A5153 n) ↔
    (∀ N : ℕ, N ≤ X → Odd N → N ∣ ∑ d ∈ N.divisors, d → N = 1) := by
  constructor
  · intro hC N hNX hodd hdiv
    by_contra h1
    have hNpos : 0 < N := hodd.pos
    have haN : a N = 1 := by
      unfold a
      rw [if_neg (by omega : ¬ _ = 0), Nat.gcd_eq_left hdiv, Nat.div_self hNpos]
    exact not_practical_of_odd hodd h1 (hC N hNpos hNX (haN ▸ practical_one))
  · intro hno n hn hnX ha
    by_contra hnp
    obtain ⟨N, hNn, -, hN1, hodd, hdiv⟩ := counterexample_structure hn ha hnp
    exact hN1 (hno N ((Nat.le_of_dvd hn hNn).trans hnX) hodd hdiv)

/-- Powers of 2 are practical. -/
lemma practical_two_pow (k : ℕ) : A5153 (2 ^ k) := by
  have h := (SC_mul_prime_pow (m := 1) one_pos Nat.prime_two (by decide) SC_one
    (by simp [sig]) k).1
  rw [one_mul] at h
  exact ⟨by positivity, SC.practical (by positivity) h⟩

/-- The special case in the OEIS comment (`a(n)` a power of 2) is equivalent to the same
statement. -/
theorem coleman_dyadic_iff_noOddMultiperfect :
    (∀ n : ℕ, 0 < n → (∃ k : ℕ, a n = 2 ^ k) → A5153 n) ↔ NoOddMultiperfect := by
  constructor
  · intro hC N hodd hdiv
    by_contra h1
    have hNpos : 0 < N := hodd.pos
    have haN : a N = 1 := by
      unfold a
      rw [if_neg (by omega : ¬ _ = 0), Nat.gcd_eq_left hdiv, Nat.div_self hNpos]
    exact not_practical_of_odd hodd h1 (hC N hNpos ⟨0, by simpa using haN⟩)
  · intro hno n hn ⟨k, hk⟩
    exact (coleman_iff_noOddMultiperfect.2 hno) n hn (hk ▸ practical_two_pow k)

/-- Coleman's conjecture at OEIS A007691 (2013): every multiply perfect number is practical. -/
def MultiperfectPracticalConjecture : Prop :=
  ∀ n : ℕ, 0 < n → n ∣ ∑ d ∈ n.divisors, d → A5153 n

/-- Coleman's conjecture at A007691 is equivalent to the same statement: every multiply
perfect number is practical iff there is no odd multiply perfect number greater than 1. In
particular the conjectures at A007691 and at A017666 are equivalent to each other. -/
theorem multiperfectPractical_iff_noOddMultiperfect :
    MultiperfectPracticalConjecture ↔ NoOddMultiperfect := by
  constructor
  · intro hC N hodd hdiv
    by_contra h1
    exact not_practical_of_odd hodd h1 (hC N hodd.pos hdiv)
  · intro hno n hn hdiv
    have haN : a n = 1 := by
      unfold a
      rw [if_neg (by omega : ¬ _ = 0), Nat.gcd_eq_left hdiv, Nat.div_self hn]
    exact (coleman_iff_noOddMultiperfect.2 hno) n hn (haN ▸ practical_one)

end A017666

#print axioms A017666.coleman_iff_noOddMultiperfect
#print axioms A017666.coleman_bounded
#print axioms A017666.counterexample_structure
#print axioms A017666.coleman_dyadic_iff_noOddMultiperfect
#print axioms A017666.multiperfectPractical_iff_noOddMultiperfect

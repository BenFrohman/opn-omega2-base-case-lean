import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

open scoped ArithmeticFunction

/-!
# ω(N) = 2 base case of Steuerwald

No odd perfect number of the form \(p^2 q\) for distinct odd primes \(p, q\).
Proof by pure \(ℕ\)-arithmetic and nlinarith.
Existence of an odd perfect number remains open.
-/

/-- Helper: for distinct odd primes p, q, 15 * (1 + p + p^2) * (1 + q) ≤ 26 * (p^2 * q). -/
private lemma abundancy_bound_nat {p q : ℕ}
    (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hpq : p ≠ q) :
    15 * (1 + p + p ^ 2) * (1 + q) ≤ 26 * (p ^ 2 * q) := by
  rcases eq_or_lt_of_le hp3 with rfl | hp4
  · -- Case p = 3, so q ≥ 5 since p ≠ q and q is odd
    have hq4 : 4 ≤ q := by omega
    nlinarith
  · -- Case p ≥ 4 and q ≥ 3
    nlinarith [sq_nonneg p, sq_nonneg q]

/-- No odd perfect number of the form p^2 * q with distinct odd primes p, q. -/
theorem no_odd_perfect_p2_q (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hodd : Odd p ∧ Odd q) :
    σ 1 (p ^ 2 * q) ≠ 2 * (p ^ 2 * q) := by
  -- 1. Distinct odd primes are ≥ 3
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    obtain ⟨k, rfl⟩ := hodd.1
    omega
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    obtain ⟨k, rfl⟩ := hodd.2
    omega
  -- 2. Expand σ₁(p^2 * q) using multiplicativity and prime power formulas
  have hcop : Nat.Coprime (p ^ 2) q := (hp.coprime_iff_not_dvd.mpr fun h =>
    hpq (Nat.Prime.eq_of_dvd_of_prime hp hq h)).pow_left 2
  have hsigma : σ 1 (p ^ 2 * q) = (1 + p + p ^ 2) * (1 + q) := by
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hcop]
    rw [ArithmeticFunction.sigma_one_apply_prime_pow hp, ArithmeticFunction.sigma_one_apply_prime hq]
    simp [Finset.sum_range_succ]
    ring
  -- 3. Combine with the integer abundancy bound
  have hbound := abundancy_bound_nat hp3 hq3 hpq
  have hpq_pos : 0 < p ^ 2 * q := by positivity
  omega

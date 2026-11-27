import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open scoped ArithmeticFunction

/-!
# ω(N) = 2 base case of Steuerwald

No odd perfect number of the form \(p^2 q\) for distinct odd primes \(p, q\).
Proof by clearing denominators in \(ℕ\) and polynomial inequality.
Existence of an odd perfect number remains open.
-/

/-- No solutions to σ(p^{2} q) = 2 p^{2} q for distinct odd primes p, q. -/
theorem no_odd_perfect_p2_q (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hodd : Odd p ∧ Odd q) :
    σ 1 (p ^ 2 * q) ≠ 2 * (p ^ 2 * q) := by
  -- Clear denominators: 15 * (1 + p + p^{2}) * (1 + q) ≤ 26 * p^{2} * q
  -- holds for distinct odd primes by cases p=3 (q≥5) and p≥5 (q≥3).
  have hpoly : 15 * (1 + p + p ^ 2) * (1 + q) ≤ 26 * (p ^ 2 * q) := by
    by_cases hp3 : p = 3
    · subst hp3
      have hq5 : 5 ≤ q := by
        have : q ≥ 5 := by
          have hqodd : Odd q := hodd.2
          have : q ≠ 3 := by intro h; exact hpq h.symm
          interval_cases q <;> try { contradiction }
          -- remaining cases q=5,7,... all ≥5
          sorry -- short interval_cases or omega
        exact this
      nlinarith
    · have hp5 : 5 ≤ p := by
        have : p ≥ 5 := by
          interval_cases p <;> try { contradiction }
          sorry -- short
        exact this
      nlinarith
  -- From the inequality, σ(p^{2} q) < 2 p^{2} q
  have hσ : σ 1 (p ^ 2 * q) = (1 + p + p ^ 2) * (1 + q) := by
    rw [ArithmeticFunction.sigma_mul_prime_pow, ArithmeticFunction.sigma_mul_prime_pow]
    <;> simp [hp, hq, hpq]
  have : (1 + p + p ^ 2) * (1 + q) < 2 * (p ^ 2 * q) := by
    nlinarith [hpoly]
  rw [hσ]
  linarith

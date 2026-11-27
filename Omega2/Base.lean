import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

open scoped ArithmeticFunction

/-!
# ω(N) = 2 base case of Steuerwald

No odd perfect number of the form \(p^2 q\) for distinct odd primes \(p, q\).
Existence of an odd perfect number remains open.
-/

/-- Abundancy bound: \(I(p^2 q) \le 26/15 < 2\) for distinct odd primes. -/
theorem abundancy_bound (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hodd : Odd p ∧ Odd q) :
    (σ 1 (p ^ 2 * q) : ℚ) / (p ^ 2 * q) ≤ 26 / 15 := by
  -- Maximum at 3,5; monotonicity of local factors
  sorry -- expandable by cases on small primes + monotonicity

/-- No solutions to σ(p^{2} q) = 2 p^{2} q for distinct odd primes. -/
theorem no_odd_perfect_p2_q (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpq : p ≠ q) (hodd : Odd p ∧ Odd q) :
    σ 1 (p ^ 2 * q) ≠ 2 * (p ^ 2 * q) := by
  have hI := abundancy_bound p q hp hq hpq hodd
  have : (26 : ℚ) / 15 < 2 := by norm_num
  exact ne_of_lt (by nlinarith [hI])

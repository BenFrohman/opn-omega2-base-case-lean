import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic

open ArithmeticFunction

/-!
# ω(N) = 2 base case of Steuerwald

No odd perfect number of the form \(p^2 q\) for distinct odd primes \(p, q\).
Existence of an odd perfect number remains open.
-/

/-- No odd perfect number of the form p ^ 2 * q with distinct odd primes p, q. -/
theorem no_odd_perfect_p2_q (p q : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hodd : Odd p ∧ Odd q) :
    sigma 1 (p ^ 2 * q) ≠ 2 * (p ^ 2 * q) := by
  have hcop : Nat.Coprime (p ^ 2) q :=
    (hp.coprime_iff_not_dvd.mpr fun h => hpq (Nat.prime_dvd_prime_iff_eq hp hq |>.mp h)).pow_left 2
  have hsig : sigma 1 (p ^ 2 * q) = (1 + p + p ^ 2) * (1 + q) := by
    rw [isMultiplicative_sigma.map_mul_of_coprime hcop,
        sigma_apply_prime_pow hp,
        sigma_apply_prime hq]
    simp [Finset.sum_range_succ]
    ring
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases hodd.1 with ⟨k, rfl⟩
    omega
  have hq3 : 3 ≤ q := by
    have := hq.two_le
    rcases hodd.2 with ⟨k, rfl⟩
    omega
  -- Direct inequality for distinct odd primes
  have hlt : (1 + p + p ^ 2) * (1 + q) < 2 * (p ^ 2 * q) := by
    nlinarith [sq_nonneg (p - 3), sq_nonneg (q - 3), hp3, hq3]
  rw [hsig]
  exact ne_of_lt hlt

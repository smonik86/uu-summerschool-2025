import Mathlib
open Finset
def B (n : ℕ) (x y : ℕ) := (x + y)^n
theorem binomial_theorem_nat (x y : ℕ) :  ∀ n : ℕ, (x + y)^n = ∑ k ∈ Ico 0 (n + 1), Nat.choose n k * x^k * y^(n - k) := by
  intro n
  induction n
  · simp
  next k ih =>
    simp
    rw[pow_add]
    simp
    rw[ih]
    rw[Finset.sum_mul]
    simp_rw[Nat.mul_add]
    rw[Finset.sum_add_distrib]
    simp
    rw[Finset.sum_range_succ]
    simp
    rw[←pow_succ]
    nth_rewrite 3[←pow_one y]
    -- rw[←pow_succ] -- not sure why this isn't working for y?
    rw [←Nat.choose_succ_right] -- pascal's identity
    nth_rewrite 4[Nat.choose_succ_succ]









    sorry

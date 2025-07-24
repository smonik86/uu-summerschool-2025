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
    rw [pow_add, ih]
    rw[]


    sorry









--  | .zero =>
    -- base case: n = 0
 --   simp only [pow_zero, range_one, Nat.choose_zero_right, pow_zero, mul_one, mul_one, sum_singleton]
  --| succ d hd =>
    -- inductive step: assume true for d, prove for d + 1
  --  rw [pow_succ, hd]
   -- rw [mul_sum]
   -- rw [← sum_range_succ']

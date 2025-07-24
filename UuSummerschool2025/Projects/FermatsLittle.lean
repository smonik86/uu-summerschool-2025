import Mathlib
def B (n : ℕ) (x y : ℕ) := (x + y)^n
theorem binomial_theorem_nat (x y : ℕ) :  ∀ n : ℕ, (x + y)^n = ∑ k in range (n + 1), Nat.choose n k * x^k * y^(n - k)
  | zero =
    -- base case: n = 0
  simp only [pow_zero, range_one, Nat.choose_zero_right, pow_zero, mul_one, mul_one, sum_singleton]
  | succ d hd =>
    -- inductive step: assume true for d, prove for d + 1
    rw [pow_succ, hd]
    rw [mul_sum]
    rw [← sum_range_succ']

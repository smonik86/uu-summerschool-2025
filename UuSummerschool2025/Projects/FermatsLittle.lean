import Mathlib
open Finset
def B (n : ℕ) (x y : ℕ) := (x + y)^n
<<<<<<< HEAD

def icoFun (k : ℕ) (x : ℕ) (hx : x ∈ Ico 0 (k + 1)) : ℕ :=  x+1
/-
lemma icoFun_bijective (k : ℕ) : Function.Bijective (icoFun k) := by
  simp[icoFun]

  sorry-/

=======
>>>>>>> d90d5c394ffc73581c1d45f1e0525c77f911d322
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
<<<<<<< HEAD
    conv =>
      lhs
      lhs
      simp[mul_assoc]
      simp[mul_comm]
      simp[← mul_assoc]
      simp[←pow_succ]

    -- rw[Finset.sum_range_succ]
    --simp
    nth_rewrite 3[←pow_one y]
    conv =>
      lhs
      rhs
      simp[mul_assoc]
    simp_rw[←pow_succ]
    have : ∑ x_1 ∈ Ico 0 (k + 1), k.choose x_1 * x ^ (x_1 + 1) * y ^ (k - x_1)   =
      ∑ x_1 ∈ Ico 1 (k + 2), k.choose (x_1 - 1) * x ^ x_1 * y ^ (k + 1 - x_1) := by
      apply Finset.sum_bij (ι := ℕ) (icoFun k)
      · unfold icoFun
        intro x hx
        simp_all
      · unfold icoFun
        simp
      · unfold icoFun
        simp
        intro x hx
        intro d
        use x - 1
        simp_all
        omega
      · unfold icoFun
        intro x hx
        simp_all
        /-conv =>
          lhs
          rw[mul_comm]
          rw[←mul_assoc]
          lhs
          rw[mul_comm]
          rw[mul_assoc]
          simp[←pow_succ]-/
    ring_nf
    simp_rw[this]



    #check Nat.choose_succ_right
    simp_rw [←Nat.choose_succ_right] -- pascal's identity
    nth_rewrite 4[Nat.choose_succ_succ]
=======
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
>>>>>>> d90d5c394ffc73581c1d45f1e0525c77f911d322

/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import UuSummerschool2025.Lectures.Analysis.Lecture

/-!
# Exercises for real analysis and linear arithmetic

Try to fill in the following `sorry`s.
-/

example : ∃ (x : ℝ), x + 37 = 42 := by
  sorry

example {a b c d : ℝ} (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  sorry

/- Hint: Argue by contradiction. -/
lemma eq_zero_of_forall_abs_lt {x : ℝ} (h : ∀ ε > 0, |x| < ε) : x = 0 := by
  sorry

section Convergence

/-- Every constant sequence is bounded. Prove this directly using the definition! -/
lemma Bounded.const (x : ℝ) : Bounded (fun _ ↦ x) := by
  rw [bounded_iff]
  sorry

/-- A sequence `a` converges to zero if and only if `|a|` converges to zero. -/
lemma ConvergesTo.zero_iff_convergesTo_abs_zero (a : ℕ → ℝ) :
    ConvergesTo a 0 ↔ ConvergesTo (fun n ↦ |a n|) 0 := by
  sorry

/-- A sequence `a` converges to `x` if and only if `n ↦ x - a n` converges to `0`. -/
lemma ConvergesTo.iff_convergesTo_sub_zero (a : ℕ → ℝ) (x : ℝ) :
    ConvergesTo a x ↔ ConvergesTo (fun n ↦ x - a n) 0 := by
  sorry

/-- If `a`, `b` and `c` are sequences with `a n ≤ b n ≤ c n` and `a` and `c` converge to `x`,
then also `b` converges to `x`. -/
lemma ConvergesTo.sandwich (a b c : ℕ → ℝ) {x : ℝ}
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n)
    (ha : ConvergesTo a x) (hc : ConvergesTo c x) :
    ConvergesTo b x := by
  sorry

/-
We now give an alternative proof of `ConvergesTo.mul`.
-/

/--
If `a` converges to `x` and `c` is a constant, then `n ↦ c * a n` converges to `c * x`.
Prove this directly without using `ConvergesTo.mul`!
-/
lemma ConvergesTo.const_mul {a : ℕ → ℝ} {x : ℝ} (c : ℝ) (h : ConvergesTo a x) :
    ConvergesTo (fun n ↦ c * a n) (c * x) := by
  sorry

/--
If `a` converges to `x` and `c` is a constant, then `n ↦ a n * c` converges to `x * c`.
Prove this without using `ConvergesTo.mul`!
-/
lemma ConvergesTo.mul_const {a : ℕ → ℝ} {x : ℝ} (c : ℝ) (h : ConvergesTo a x) :
    ConvergesTo (fun n ↦ a n * c) (x * c) := by
  sorry

/--
If `a` and `b` converge to `0`, also `a * b` converges to `0`.
Prove this directly without using `ConvergesTo.mul`!
-/
lemma ConvergesTo.mul_zero {a b : ℕ → ℝ} (ha : ConvergesTo a 0) (hb : ConvergesTo b 0) :
    ConvergesTo (a * b) 0 := by
  sorry

/--
If `a` converges to `x` and `b` converges to `y`, then `a * b` converges
to `x * y`.
Prove this directly using the above lemmas without using `ConvergesTo.mul`!
-/
example {a b : ℕ → ℝ} {x y : ℝ} (ha : ConvergesTo a x)
    (hb : ConvergesTo b y) :
    ConvergesTo (a * b) (x * y) := by
  rw [ConvergesTo.iff_convergesTo_sub_zero]
  sorry

/-- If `a` converges to both `x` and `y`, `x = y`. -/
lemma ConvergesTo.unique (a : ℕ → ℝ) {x y : ℝ} (hx : ConvergesTo a x) (hy : ConvergesTo a y) :
    x = y := by
  sorry

end Convergence

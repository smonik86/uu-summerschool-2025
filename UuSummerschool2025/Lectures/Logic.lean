import Mathlib

/-!

# Lecture 1: Logic and Sets: Logic

In this first lecture, we're going to explore how to prove basic statements
in propositional and predicate logic in lean, and we're also going to see
how to work with sets and functions.

-/

section
/-!
## Logical connectives, some examples

The way we prove a statement in logic depends a little bit on the *logical
connectives* involved, so we'll organise our discussion around that. First,
let's discuss *implication*.
-/


/-! ### Implications
To write the symbol `→`, use `\to`.

Relevant tactics:

When in goal: `intro`/`intros`
When in hypothesis: `have` or `specialize`
-/

example (p : Prop) : p → p := sorry


example (p q : Prop) : p → (q → p) := sorry


example (p q r : Prop) : (p → q) → ((p → (q → r)) → (p → r)) := sorry


/-! ### Universal quantification

To write the `∀` symbol, use `\forall`

The same tactics used in implications are relevant here.
-/

/-
This is just another way of writing our first example
-/
example : ∀ p : Prop, p → p := sorry

example (α : Type) (p q : α → Prop) (h : ∀ x, p x → q x) :
    (∀ x, p x) → ∀ x', q x' := sorry


/-! ### Existential quantifier

To write the `∃` symbol, use `\exists`

Relevant tactics:

When in goal: `use`
When in hypothesis: `obtain`
-/

example : ∃ n : ℕ, n < n + 1 := sorry

example : ∃ n : ℕ, n = n := sorry

example (f : ℕ → ℕ)
    (hf : ∀ m, ∃ n, m ≤ f n) :
    ∀ m, ∃ n, m ≤ 2 * f n := sorry



/-! ### Conjunctions

To write the `∧` symbol, use `\and`

Relevant tactics:

When in goal: `constructor` (or `use`)
When in hypothesis: `obtain`

If `h : p ∧ q` then `h.1 : p` and `h.2 : q`.
We can also say `h.left` or `h.right`
-/

example (p q : Prop) : p → q → p ∧ q := sorry


example (p q : Prop) : p ∧ q → q ∧ p := sorry

/-! ### Disjunctions

To write the `∨` sumbol, use `\or`

Relevant tactics:

When in goal: `left`/`right`
When in hypothesis: `obtain`
-/

example (p q : Prop) : p → p ∨ q := sorry


example (p q : Prop) : p ∨ q → q ∨ p := sorry


/-! ### Iffs

To write the `↔` symbol, use `\iff`

Relevant tactics:

When in goal: `constructor`/`use`

When in hypothesis: `rw`/`simp`/etc. since we
can rewrite with `↔` statements.

If `h : p ↔ q` then `h.mp : p → q` and `h.mpr : q → p`
-/

example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) := sorry

/-! ### Negation

To write the `¬` symbol, use `\not`

Relevant tactics:

When in goal: `intro`
When in hypothesis: `apply` (if goal is `False`), `have`

Note:
`contrapose!` and `push_neg` are useful for manipulating negations too.
-/

/-
`¬ p` is actually *defined* in lean to be `p → False`. So we can just work with
it like any other implication.
-/
example (p : Prop) : ¬ p ↔ (p → False) := Iff.rfl

example (p q : Prop) (h : p → q) : ¬ q → ¬ p := sorry


/-
From `False` we can derive anything.
-/
example (p q : Prop) (hp : p) (hpq : ¬ p) : q := by
  exact absurd hp hpq
  -- or contradiction
  -- or exact (hpq hp).elim


example (p : Prop) (hp : ¬ ¬ p) : p := by
  push_neg at hp
  exact hp


example (p q : Prop) (h : ¬ p → ¬ q) : q → p := by
  contrapose
  exact h

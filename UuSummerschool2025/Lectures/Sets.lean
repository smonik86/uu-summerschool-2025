import Mathlib

/-! # Lecture 1: Logic and Sets: Sets -/

namespace MyDefs

/--

In Mathlib, a set of elements of `α` is a predicate with domain `α`,
i.e. a function `p : α → Prop`. The idea is that for some `x : α`,
`p a` should be true if `a` is in the set and false otherwise.

We denote the type of all such functions by `Set α`.
If we regard `α` as iteslf being a set, then the type `Set α`
is the power set of `α`. -/

def Set (α : Type*) := (α → Prop)

variable {α : Type*}

/--
Interpret a predicate `p : α → Prop` as a set.
 -/
def setOf (p : α → Prop) : Set α := p

/--
Given a set `s : Set α` and a `x : α`, `Set.mem s x` is proposition
that `x` is an element of `s`.
 -/
def Set.mem (s : Set α) (x : α) : Prop := sorry

/-- Enable `∈` notation. -/
instance : Membership α (Set α) := sorry



/-
This says that Set.mem is really just the proposition that the set is
defined to be
-/
lemma Set.mem_iff (x : α) (s : Set α) : x ∈ s ↔ s x := sorry



/-
The following gives an error when uncommented. This is because
even though `Set α` and `α → Prop` are the same under the hood,
lean wants you to use the `Set α` notation in order for the
`∈` notation to work.
-/

--example (x : α) (s : α → Prop) : x ∈ s ↔ s x := Iff.rfl

/-
When defining new data structures, we often write "extensionality"
lemmas (usually denoted with `_.ext`). These say that "two things are the same
if they contain the same stuff".

For example, we have `funext`, which says that two functions `f g : α → β`
are equal if `f x = g x` for all `x : α`.

We also have `propext`, which says that two propositions `a` and `b` are
equal if `a ↔ b`.

We're going to show an extensionality lemma for sets `Set.ext`,
which says that two sets are equal iff they have the same elements.
-/
#check funext
#check propext

lemma Set.ext (s t : Set α) : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t := sorry

/-
We can make our own notation using the *notation* keyword. Here,
we're making a notation which resembles the familiar set builder notation.

Note that lean already has a built in set builder notation, so we've added
this funny `my` at the start so that lean doesn't complain.
-/
notation "my{" x " | " p "}" => setOf fun x => p

#check my{(n : Nat) | 0 < n}


/-
Write the following common set operations using our set builder notation:
-/

/-- s ∪ t -/
def Set.union (s t : Set α) : Set α := sorry

/-- s ∩ t -/
def Set.inter (s t : Set α) : Set α := sorry

/-- s \ t -/
def Set.diff (s t : Set α) : Set α := sorry

/-- sᶜ -/
def Set.compl (s : Set α) : Set α := sorry

/-- s ⊆ t -/
def Set.IsSubset (s t : Set α) : Prop := ∀ x, x ∈ s → x ∈ t

/-- ∅ -/
def Set.empty : Set α := sorry

/-- Set.univ : Set α should be α regarded as a set -/
def Set.univ : Set α := sorry

lemma Set.mem_setOf (p : α → Prop) (x : α) :
  x ∈ my{x' | p x'} ↔ p x := sorry

lemma Set.mem_union (s t : Set α) (x : α) :
    x ∈ Set.union s t ↔ x ∈ s ∨ x ∈ t := sorry

lemma Set.mem_inter_iff (s t : Set α) (x : α) :
    x ∈ Set.inter s t ↔ x ∈ s ∧ x ∈ t := sorry

#check Set.mem_diff
#check Set.mem_compl_iff
#check Set.subset_def

end MyDefs


open Set

/-
From this point on we have exited the `MyDefs` namespace and are just
working with the existing `Set` library in lean. This is just so we have
access to more lemmas so we can prove more interesting statements, the
lean library under the hood looks more or less like what we've developed
above.
-/


variable {α β : Type*} (s t u : Set α)

/-
The following is a fairly simple set theory lemma, and we're going to prove
it in a few different ways
-/

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := sorry
  /-
  We can prove this in a verbose style, by using rw? to guide us
  -/


example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  /-
  In fact, we do not need to explicitly unfold the definitions here,
  we can just use intro directly here.
  -/
  sorry


example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  /-
  This must exist somewhere in the library, we can also
  solve this problem by trying to find this lemma.
  -/
  sorry

example : s ∪ t = t ∪ s := by
  ext x
  rw[mem_union, mem_union, Or.comm]


/-! ## Functions -/

/-
So far we have seen the `→` symbol used for implications, but it can also
be used to denote functions! In fact, this is more than just a notational
trick, as we have seen under the hood these are really the same thing.
-/
variable (f : α → β)

/-
Here we can define function composition, and notice how it's exactly
the same as proving the transitivity of implication.
-/
example {γ : Type*} (g : α → β) (h : β → γ) : α → γ := sorry

#check Set.preimage
example (s : Set β) : f ⁻¹' s = {x | f x ∈ s} := rfl

#check Set.image
example (s : Set α) : f '' s = {y | ∃ x, x ∈ s ∧ f x = y} := rfl

#check Set.mem_preimage
-- Can do `rw [Set.preimage]`

#check Set.mem_image
-- Can do `rw [Set.image]`

example (u v : Set β) : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  unfold preimage
  rw [@union_def]
  rw [← setOf_or]
  ext a
  rw[mem_setOf, mem_setOf, mem_setOf]

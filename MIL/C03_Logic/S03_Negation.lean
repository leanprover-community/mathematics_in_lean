import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  sorry

example : ¬FnHasUb fun x ↦ x :=
  sorry

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)

example (h : Monotone f) (h' : f a < f b) : a < b := by
  -- aesop?
  contrapose! h'
  exact h h'

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  -- aesop?
  apply Aesop.BuiltinRules.not_intro
  intro a_1
  apply not_lt_of_ge _ h'
  simp_all only [ge_iff_le]
  exact a_1 h

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := -- by suggest_tactics
                             -- by aesop?
                             by rename_i f_1
                                simp_all only
                                exact monotone_const
  have h' : f 1 ≤ f 0 := le_refl _
  sorry

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  -- aesop?
  simp_all only [gt_iff_lt]
  contrapose! h
  exact ⟨x, h, le_refl _⟩

end

section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  -- suggest_tactics
  -- aesop?
  intro x
  simp_all only [not_exists, not_false_eq_true]

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  -- suggest_tactics
  -- aesop?
  simp_all only [exists_false, not_false_eq_true]

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  -- suggest_tactics
  -- aesop?
  simp_all only [not_forall]

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  -- suggest_tactics
  -- aesop?
  simp_all only [not_forall]

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

example (h : ¬¬Q) : Q := by
  -- suggest_tactics
  -- aesop?
  simp_all only [not_not]

example (h : Q) : ¬¬Q := by
  -- suggest_tactics
  -- aesop?
  simp_all only [not_true, not_false_eq_true]

end

section
variable (f : ℝ → ℝ)

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  -- aesop?
  intro a
  simp_all only [gt_iff_lt]
  by_contra' H
  exact h ⟨a, H⟩

example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h

example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  -- aesop?
  contrapose! h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end

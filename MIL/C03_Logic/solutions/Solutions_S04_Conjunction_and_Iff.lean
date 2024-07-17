import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  rcases h with ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply Nat.dvd_antisymm h0 h2

example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply le_antisymm h0 h2

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · exact aux h
    rw [add_comm] at h
    exact aux h
  rintro ⟨rfl, rfl⟩
  norm_num

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff]
  use 0, 1
  norm_num

section
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_le]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply le_antisymm h0 h2

end

section
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_le]
  rintro ⟨h0, h1⟩
  exact h1 h0

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_le]
  rintro ⟨h0, h1⟩ ⟨h2, h3⟩
  constructor
  · apply le_trans h0 h2
  intro h4
  apply h1
  apply le_trans h2 h4

end

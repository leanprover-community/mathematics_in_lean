import Mathlib.Data.Real.Basic

namespace C03S05
section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < abs y → x < y ∨ x < -y := by
  cases' le_or_gt 0 y with h h
  · rw [abs_of_nonneg h]
    intro h
    left
    exact h
  rw [abs_of_neg h]
  intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ abs x := by
  sorry

theorem neg_le_abs_self (x : ℝ) : -x ≤ abs x := by
  sorry

theorem abs_add (x y : ℝ) : abs (x + y) ≤ abs x + abs y := by
  sorry

theorem lt_abs : x < abs y ↔ x < y ∨ x < -y := by
  sorry

theorem abs_lt : abs x < y ↔ -y < x ∧ x < y := by
  sorry

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with (xlt | xeq | xgt)
  · left
    exact xlt
  · contradiction
  right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with (⟨a, rfl⟩ | ⟨b, rfl⟩)
  · rw [mul_assoc]
    apply dvd_mul_right
  rw [mul_comm, mul_assoc]
  apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  sorry

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

section
variable {R : Type _} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry


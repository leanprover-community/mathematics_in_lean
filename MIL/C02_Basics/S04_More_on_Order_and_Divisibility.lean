import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  -- suggest_tactics
  -- aesop?
  rw [max_comm]

example : min (min a b) c = min a (min b c) := by
  -- aesop?
  simp [min_def]
  split
  · split
    · split
      · simp_all only
      · simp_all only [not_le]
    · simp_all only [not_le]
      split
      · nlinarith
      · simp_all only [not_le]
        split
        · linarith
        · simp_all only [not_le]
  · simp_all only [not_le]
    split
    · split
      · linarith
      · simp_all only [not_le]
    · simp_all only [not_le]
      split
      · linarith
      · simp_all only [not_le]

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  -- suggest_tactics
  -- aesop?
  simp_all only [ge_iff_le, add_le_add_iff_right, le_min_iff, min_le_iff, le_refl, true_or, or_true, and_self]

example : min a b + c = min (a + c) (b + c) := by
  -- aesop?
  cases' le_total a b with h h
  · simp_all only [ge_iff_le, min_eq_left, add_le_add_iff_right]
  · simp_all only [ge_iff_le, min_eq_right, add_le_add_iff_right]

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  sorry

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
   apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  sorry
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  -- suggest_tactics
  -- aesop?
  rw [Nat.gcd_comm]
end

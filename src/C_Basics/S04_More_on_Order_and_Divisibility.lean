import Mathlib.Data.Real.Basic

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
  sorry

example : min (min a b) c = min a (min b c) := by
  sorry

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  sorry

example : min a b + c = min (a + c) (b + c) := by
  sorry

#check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)

example : abs a - abs b ≤ abs (a - b) :=
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

open Nat

#check (gcd_zero_right n : gcd n 0 = n)

#check (gcd_zero_left n : gcd 0 n = n)

#check (lcm_zero_right n : lcm n 0 = 0)

#check (lcm_zero_left n : lcm 0 n = 0)

example : gcd m n = gcd n m := by
  sorry

end



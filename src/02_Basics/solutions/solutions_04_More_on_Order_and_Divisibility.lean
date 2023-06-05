import data.real.basic

section
variables a b c d : ℝ

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : max a b = max b a :=
begin
  apply le_antisymm,
  repeat {
    apply max_le,
    apply le_max_right,
    apply le_max_left }
end

example : min (min a b) c = min a (min b c) :=
begin
  apply le_antisymm,
  { apply le_min,
    { apply le_trans,
      apply min_le_left,
      apply min_le_left },
    apply le_min,
    { apply le_trans,
      apply min_le_left,
      apply min_le_right },
    apply min_le_right  },
  apply le_min,
  { apply le_min,
    { apply min_le_left },
    apply le_trans,
    apply min_le_right,
    apply min_le_left },
  apply le_trans,
  apply min_le_right,
  apply min_le_right
end

lemma aux : min a b + c ≤ min (a + c) (b + c) :=
begin
  apply le_min,
  { apply add_le_add_right,
    apply min_le_left },
  apply add_le_add_right,
  apply min_le_right
end

example : min a b + c = min (a + c) (b + c) :=
begin
  apply le_antisymm,
  { apply aux },
  have h : min (a + c) (b + c) = min (a + c) (b + c) - c + c,
  { rw sub_add_cancel },
  rw h,
  apply add_le_add_right,
  rw sub_eq_add_neg,
  apply le_trans,
  apply aux,
  rw [add_neg_cancel_right, add_neg_cancel_right]
end

example : abs a - abs b ≤ abs (a - b) :=
calc
  abs a - abs b = abs (a - b + b) - abs b :
    by rw sub_add_cancel
  ... ≤ abs (a - b) + abs b - abs b :
    begin
      apply sub_le_sub_right,
      apply abs_add
    end
  ... ≤ abs (a - b) :
    by rw add_sub_cancel

-- alternatively
example : abs a - abs b ≤ abs (a - b) :=
begin
  have h := abs_add (a - b) b,
  rw sub_add_cancel at h,
  linarith
end

end

section
variables w x y z : ℕ

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
dvd_trans h₀ h₁

example : x ∣ y * x * z :=
begin
  apply dvd_mul_of_dvd_left,
  apply dvd_mul_left
end

example : x ∣ x^2 :=
by apply dvd_mul_right

example (h : x ∣ w) : x ∣ y * (x * z) + x^2 + w^2 :=
begin
  apply dvd_add,
  { apply dvd_add,
    { apply dvd_mul_of_dvd_right,
      apply dvd_mul_right },
    apply dvd_mul_right },
  rw pow_two,
  apply dvd_mul_of_dvd_right,
  exact h
end

end

section
variables m n : ℕ
open nat

#check (gcd_zero_right n : gcd n 0 = n)
#check (gcd_zero_left n  : gcd 0 n = n)
#check (lcm_zero_right n : lcm n 0 = 0)
#check (lcm_zero_left n  : lcm 0 n = 0)

example : gcd m n = gcd n m :=
begin
  apply dvd_antisymm,
  repeat {
    apply dvd_gcd,
    apply gcd_dvd_right,
    apply gcd_dvd_left }
end

end

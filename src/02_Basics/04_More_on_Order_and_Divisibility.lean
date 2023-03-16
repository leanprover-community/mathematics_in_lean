import data.real.basic

section
variables a b c d : ℝ

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a :=
begin
  apply le_antisymm,
  { show min a b ≤ min b a,
    apply le_min,
    { apply min_le_right },
    apply min_le_left },
  { show min b a ≤ min a b,
    apply le_min,
    { apply min_le_right },
    apply min_le_left }
end

example : min a b = min b a :=
begin
  have h : ∀ x y, min x y ≤ min y x,
  { intros x y,
    apply le_min,
    apply min_le_right,
    apply min_le_left },
  apply le_antisymm, apply h, apply h
end

example : min a b = min b a :=
begin
  apply le_antisymm,
  repeat {
    apply le_min,
    apply min_le_right,
    apply min_le_left }
end

example : max a b = max b a :=
begin
  have h : ∀ x y, max x y ≤ max y x,
  {
    intros x y,
    apply max_le,
    apply le_max_right,
    apply le_max_left,
  },
  apply le_antisymm,
  apply h,
  apply h,
end

-- -- backup
-- example : min (min a b) c = min a (min b c) := begin
--   have x₀ : ∀ x y z, min (min x y) z ≤ x, { 
--     intros x y z,
--     apply le_trans,
--     { show min (min x y) z ≤ (min x y),
--     -- apply le_min,
--     -- apply min_le_left,
--     -- apply min_le_right,
--       sorry,},
--     apply min_le_left,
--     -- have xx₀ : min (min x y) z ≤ min x y, by apply min_le_left,
--     -- have xx₁ : min x y ≤ x, by apply min_le_left,
--     -- apply le_trans xx₀ xx₁,
--   },
--   have x₁ : min (min a b) c ≤ b, sorry,
--   have x₂ : min (min a b) c ≤ c, sorry,
-- sorry,
-- end

example : min (min a b) c = min a (min b c) := begin
  apply le_antisymm,
  { 
    show min (min a b) c ≤ min a (min b c),
    have h₀ : min (min a b) c ≤ min a b, by apply min_le_left,
    have h₁ : min a b ≤ a, by apply min_le_left,
    have h₂ : min (min a b) c ≤ a, begin
      apply le_trans h₀ h₁,
    end,

    have z₀ : min (min a b) c ≤ min a b, by apply min_le_left,
    have z₁ : min a b ≤ b, by apply min_le_right,
    have i₀ : min (min a b) c ≤ b, begin
      apply le_trans z₀ z₁,
    end,
    have i₁ : min (min a b) c ≤ c, by apply min_le_right,
    have i₂ : min (min a b) c ≤ min b c, begin
      apply le_min i₀ i₁,
    end,

    apply le_min h₂ i₂,
  },
  { 
    show min a (min b c) ≤ min (min a b) c ,

    have h₂ : min a (min b c) ≤ b, begin
      apply le_trans,
      apply min_le_right,
      apply min_le_left,
    end,
    have h₁ : min a (min b c) ≤ a, begin
      apply min_le_left,
    end,
    have h₀ : min a (min b c) ≤ min a b, begin
      apply le_min h₁ h₂,
    end,

    have i₀ : min a (min b c) ≤ c, begin
     apply le_trans,
     apply min_le_right,
     apply min_le_right,
    end,
    apply le_min h₀ i₀
  },
end

lemma aux : min a b + c ≤ min (a + c) (b + c) := begin
  apply le_min,
  { 
    have h₀ : min a b ≤ a, by apply min_le_left,
    have h₁ : min a b + c ≤ a + c, by apply add_le_add_right h₀ c,
    exact h₁,
  },
  { show min a b + c ≤ b + c,
    have h₀ : min a b ≤ b, by apply min_le_right,
    have h₁ : min a b + c ≤ b + c, by apply add_le_add_right h₀ c,
    exact h₁,
  },
end

example : min a b + c = min (a + c) (b + c) := begin
  apply le_antisymm,
  { show  min a b + c ≤ min (a + c) (b + c),
  apply aux,
  },
  { show min (a + c) (b + c) ≤ min a b + c,
    have h₂ : min (a + c) (b + c) + -c ≤ min a b, begin
      apply le_min,
      {  show min (a + c) (b + c) + -c ≤ a,
        have i₀ : min (a + c) (b + c) ≤ a + c, by apply min_le_left,
        have i₁ : min (a + c) (b + c) + -c ≤ a + c + -c, by apply add_le_add_right i₀,
        rw add_neg_cancel_right at i₁,
        exact i₁,
      },
      { show min (a + c) (b + c) + -c ≤ b,
        have i₀ : min (a + c) (b + c) ≤ b + c, by apply min_le_right,
        have i₁ : min (a + c) (b + c) + -c ≤ b + c + -c, by apply add_le_add_right i₀,
        rw add_neg_cancel_right at i₁,
        exact i₁,
      },
    end,
    have h₃ : min (a + c) (b + c) + -c + c ≤ min a b + c, begin
      apply add_le_add_right h₂,
    end,
    by linarith,
  }
end

#check (abs_add : ∀ a b : ℝ, abs (a + b) ≤ abs a + abs b)

#check sub_add_cancel --  a - b + b = a

example : abs a - abs b ≤ abs (a - b) := begin
  have h₀ : abs (a - b + b) ≤ abs (a - b) + abs b, by apply abs_add,
  have h₁ : abs a <= abs (a - b) + abs b, by { rw sub_add_cancel at h₀, exact h₀ },
  by linarith,
end

end

section
variables w x y z : ℕ

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
dvd_trans h₀ h₁

example : x ∣ y * x * z :=
begin
  apply dvd_mul_of_dvd_left,
  apply dvd_mul_left,
end

example : x ∣ x^2 :=
by apply dvd_mul_right

example : x * x = x ^ 2 := begin
  exact (sq x).symm,
end

example : x ∣ x * y  := begin
exact dvd_mul_right x y,
  -- exact dvd.intro y rfl,
end
example : x * (y * z) = y * (x * z) := begin
  exact mul_left_comm x y z,
end

example (h : x ∣ w) : x ∣ w^2 := begin
  apply dvd_trans h,
  apply dvd_mul_right,
end

example (h : x ∣ w) (h₁ : x ∣ y) : x ∣ y + w := begin
exact dvd_add h₁ h,
end

example (h : x ∣ w) : x ∣ y * (x * z) + x^2 + w^2 := begin
  apply dvd_add,
  apply dvd_add,
  { show x ∣ y * (x * z),
    rw mul_comm,
    rw mul_assoc,
    apply dvd_mul_right,
  },
  { show x ∣ x^2,
    apply dvd_mul_right,
  },
  { show x ∣ w^2,
    apply dvd_trans h,
    apply dvd_mul_right,
  },
end

end

section
variables m n : ℕ
open nat

#check (gcd_zero_right n : gcd n 0 = n)
#check (gcd_zero_left n  : gcd 0 n = n)
#check (lcm_zero_right n : lcm n 0 = 0)
#check (lcm_zero_left n  : lcm 0 n = 0)

example : gcd m n ∣ m := begin
  exact gcd_dvd_left m n,
end

example : gcd m n ∣ n := begin
  exact gcd_dvd_right m n,
end

example (x : ℕ) (h: x ∣ n) (h₁ : x ∣ m) : x ∣ gcd m n := begin
 exact dvd_gcd h₁ h,
end

example : gcd m n = gcd n m := begin
  have h₀ : gcd m n ∣ gcd n m, begin
    apply dvd_gcd,
    exact gcd_dvd_right m n,
    exact gcd_dvd_left m n,
  end,
  have h₁ : gcd n m ∣ gcd m n, begin
    apply dvd_gcd,
    exact gcd_dvd_right n m,
    exact gcd_dvd_left n m,
  end,
  apply dvd_antisymm h₀ h₁,
end

end


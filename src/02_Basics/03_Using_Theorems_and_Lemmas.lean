import analysis.special_functions.log.basic

variables a b c d e : ℝ
open real

#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

section
variables (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  apply le_trans,
  { apply h₀ },
  -- apply h₀,
  apply h₁,
end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  apply le_trans h₀,
  apply h₁
end

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
by exact le_trans h₀ h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
le_trans h₀ h₁

example (x : ℝ) : x ≤ x :=
by apply le_refl

example (x : ℝ) : x ≤ x :=
by exact le_refl x

example (x : ℝ) : x ≤ x :=
le_refl x

#check (le_refl  : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)

/- Try this. -/

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
    (h₃ : d < e) :
  a < e := begin
  apply lt_of_le_of_lt h₀, -- b < e
  apply lt_trans h₁, -- c < e
  apply lt_of_le_of_lt h₂ h₃,
end

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d)
    (h₃ : d < e) :
  a < e :=
by linarith

section
example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) :
  d + a ≤ 5 * b :=
by linarith
end

example (h : 1 ≤ a) (h' : b ≤ c) :
  2 + a + exp b ≤ 3 * a + exp c :=
by linarith [exp_le_exp.mpr h']

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)

#check @add_le_add_left
example (h : a ≤ b) : exp a ≤ exp b :=
begin
  rw exp_le_exp,
  exact h
end

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e :=
begin
  apply add_lt_add_of_lt_of_le,
  { apply add_lt_add_of_le_of_lt h₀,
    apply exp_lt_exp.mpr h₁ },
  apply le_refl
end

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) :=
begin
  apply add_le_add_left,
  apply exp_le_exp.mpr,
  apply add_le_add_left,
  apply h₀,
end

example : (0 : ℝ) < 1 :=
by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) :=
begin
  have h₀ : 0 < 1 + exp a,
  { 
    apply lt_trans,
    apply exp_pos a,
    nth_rewrite 0 ←zero_add (exp a),
    apply add_lt_add_right,
    by norm_num,
   },
  have h₁ : 0 < 1 + exp b,
  {
    apply lt_trans,
    apply exp_pos b,
    nth_rewrite 0 ←zero_add (exp b),
    apply add_lt_add_right,
    by norm_num,
  },
  apply (log_le_log h₀ h₁).mpr,
  apply add_le_add_left,
  apply exp_le_exp.mpr,
  apply h,
end

    example : 0 ≤ a^2 :=
    begin
      -- library_search,
      exact pow_two_nonneg a
    end

example (h : a ≤ b) : c - exp b ≤ c - exp a :=
begin
  -- apply add_le_add_left,
  -- library_search,
  -- hint
  refine add_le_add _ _,
  exact rfl.ge,
  have h₁ : exp a ≤ exp b, {
    exact exp_le_exp.mpr h,
  },
  exact neg_le_neg h₁,
  -- library_search,
  -- sorry
end

example : 2*a*b ≤ a^2 + b^2 :=
begin
  have h : 0 ≤ a^2 - 2*a*b + b^2,
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2     : by ring
    ... ≥ 0                           : by apply pow_two_nonneg,
  calc
    2*a*b
        = 2*a*b + 0                   : by ring
    ... ≤ 2*a*b + (a^2 - 2*a*b + b^2) : add_le_add (le_refl _) h
    ... = a^2 + b^2                   : by ring
end

example : 2*a*b ≤ a^2 + b^2 :=
begin
  have h : 0 ≤ a^2 - 2*a*b + b^2,
  calc
    a^2 - 2*a*b + b^2 = (a - b)^2 : by ring
    ... ≥ 0                       : by apply pow_two_nonneg,
  linarith
end

example : abs (a*b) ≤ (a^2 + b^2) / 2 :=
begin
  have h₃ : 0 ≤ a^2 + b^2 + 2*a*b,
  calc
    a^2 + b^2 + 2*a*b = (a + b)^2 : by ring
    ... ≥ 0 : by apply pow_two_nonneg,
  have h₄ : 0 ≤ a^2 + b^2 - 2*a*b,
  calc
    a^2 + b^2 - 2*a*b = (a - b)^2 : by ring
    ... ≥ 0 : by apply pow_two_nonneg,
  have h₀ : a*b ≤ (a^2 + b^2) / 2,
  calc
    (a^2 + b^2) / 2 = (a^2 + b^2 - 2*a*b) / 2 + a*b : by ring
    ... ≥ a*b : by linarith, 
  have h₁ : -(a*b) ≤ (a^2 + b^2) / 2,
  calc
    (a^2 + b^2) / 2 = (a^2 + b^2 + 2*a*b) / 2 + -(a*b) : by ring
    ... ≥ -(a*b) : by linarith, 
  apply abs_le'.mpr,
  exact ⟨h₀, h₁⟩,
end

#check abs_le'.mpr


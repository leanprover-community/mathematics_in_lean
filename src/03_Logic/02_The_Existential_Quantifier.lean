import data.real.basic

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  use 5 / 2,
  norm_num
end

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
begin
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3,
    by norm_num,
  exact ⟨5 / 2, h⟩
end

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
⟨5 / 2, by norm_num⟩

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a


theorem fn_ub_add {f g : ℝ → ℝ} {a b : ℝ}
    (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

section
variables {f g : ℝ → ℝ}

example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (λ x, f x + g x) :=
begin
  cases ubf with a ubfa,
  cases ubg with b ubfb,
  use a + b,
  apply fn_ub_add ubfa ubfb
end

theorem fn_lb_add {f g : ℝ → ℝ} {a b : ℝ}
    (hfa : fn_lb f a) (hgb : fn_lb g b) :
  fn_lb (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)

example (lbf : fn_has_lb f) (lbg : fn_has_lb g) :
  fn_has_lb (λ x, f x + g x) := begin
  cases lbf with a lbfa,
  cases lbg with b lbgb,
  use a + b,
  apply fn_lb_add lbfa lbgb,
end

theorem fn_ub_mul {f : ℝ → ℝ} {a c: ℝ}
    (hfa : fn_ub f a) (cge0 : 0 ≤ c):
  fn_ub (λ x, c * f x) (c * a) := 
λ x, mul_le_mul_of_nonneg_left (hfa x) cge0 
--   begin
--   intros x,
--   change  c * f x ≤ c * a,
--   apply mul_le_mul_of_nonneg_left,
--   apply hfa x,
--   apply cge0,
-- end
-- λ x, mul_le_mul (le_refl c) (hfa x) fage0 cge0 

example {c : ℝ} (ubf : fn_has_ub f) (h : c ≥ 0):
  fn_has_ub (λ x, c * f x) := begin
  cases ubf with a ubfa,
  use c * a,
  apply fn_ub_mul ubfa h,
end

example (ubf : fn_has_ub f) (ubg : fn_has_ub g) :
  fn_has_ub (λ x, f x + g x) :=
begin
  rcases ubf with ⟨a, ubfa⟩,
  rcases ubg with ⟨b, ubfb⟩,
  exact ⟨a + b, fn_ub_add ubfa ubfb⟩
end

example : fn_has_ub f → fn_has_ub g →
  fn_has_ub (λ x, f x + g x) :=
begin
  rintros ⟨a, ubfa⟩ ⟨b, ubfb⟩,
  exact ⟨a + b, fn_ub_add ubfa ubfb⟩
end

example : fn_has_ub f → fn_has_ub g →
  fn_has_ub (λ x, f x + g x) :=
λ ⟨a, ubfa⟩ ⟨b, ubfb⟩, ⟨a + b, fn_ub_add ubfa ubfb⟩

end

section
variables {α : Type*} [comm_ring α]

def sum_of_squares (x : α) := ∃ a b, x = a^2 + b^2

theorem sum_of_squares_mul {x y : α}
    (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
  sum_of_squares (x * y) :=
begin
  rcases sosx with ⟨a, b, xeq⟩,
  rcases sosy with ⟨c, d, yeq⟩,
  rw [xeq, yeq],
  use [a*c - b*d, a*d + b*c],
  ring
end
theorem sum_of_squares_mul' {x y : α}
    (sosx : sum_of_squares x) (sosy : sum_of_squares y) :
  sum_of_squares (x * y) :=
begin
  -- 뭔지 모르겠네
  rcases sosx with ⟨a, b, rfl⟩,
  rcases sosy with ⟨c, d, rfl⟩,
  use [a*c - b*d, a*d + b*c],
  ring
end

end
section
variables {a b c : ℕ}

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c :=
begin
  cases divab with d beq,
  cases divbc with e ceq,
  rw [ceq, beq],
  use (d * e), ring
end

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ (b + c) :=
begin
  rcases divab with ⟨ d, rfl ⟩,
  rcases divac with ⟨ e, rfl ⟩,
  use (d + e), ring,
end
-- begin
--   cases divab with d beqad,
--   cases divac with e ceqae,
--   rw beqad,
--   rw ceqae,
--   use (d + e), ring,
-- end

end

section
open function

example {c : ℝ} : surjective (λ x, x + c) :=
begin
  intro x,
  use x - c,
  dsimp, ring
end

example {c : ℝ} (h : c ≠ 0) : surjective (λ x, c * x) :=
begin
  intro x,
  use x / c,
  dsimp,
  rw ← mul_div_assoc,
  rw mul_comm,
  rw (mul_div_cancel x),
  exact h,
end

example (x y : ℝ) (h : x - y ≠ 0) : (x^2 - y^2) / (x - y) = x + y :=
by { field_simp [h], ring }

example {f : ℝ → ℝ} (h : surjective f) : ∃ x, (f x)^2 = 4 :=
begin
  cases h 2 with x hx,
  use x,
  rw hx,
  norm_num
end

end

section
open function
variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

example (surjg : surjective g) (surjf : surjective f) :
  surjective (λ x, g (f x)) :=
  begin
  intro x,
  dsimp,
  -- cases 
  -- cases surjg with aa bb,
  cases surjg x with y gyx,
  cases surjf y with z fzy,
  use z,
  rw fzy,
  rw gyx,
end

end

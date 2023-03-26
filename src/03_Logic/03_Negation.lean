import data.real.basic

section
variables a b : ℝ

example (h : a < b) : ¬ b < a :=
begin
  intro h',
  have : a < a,
    from lt_trans h h',
  apply lt_irrefl a this
end

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variable f : ℝ → ℝ

example (h : ∀ a, ∃ x, f x > a) : ¬ fn_has_ub f :=
begin
  intros fnub,
  cases fnub with a fnuba,
  cases h a with x hx,
  have : f x ≤ a,
    from fnuba x,
  linarith
end

example (h : ∀ a, ∃ x, f x < a) : ¬ fn_has_lb f :=
begin
  intros fnlb,
  cases fnlb with a fnlba,
  cases h a with x flta,
  have : f x ≥ a,
    from fnlba x,
  linarith,
end

#check fn_ub
-- def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a

example : ¬ fn_has_ub (λ x, x) :=
begin
  intros fnub,
  cases fnub with a fnuba,

  have :a + 1 ≤ a, from fnuba (a + 1),
  linarith,
end

#check (not_le_of_gt : a > b → ¬ a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬ a < b)
#check (lt_of_not_ge : ¬ a ≥ b → a < b)
#check (le_of_not_gt : ¬ a > b → a ≤ b)

-- def monotone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f a ≤ f b
example (h : monotone f) (h' : f a < f b) : a < b :=
begin
  apply lt_of_not_ge,
  intros agteb,
  have : f b ≤ f a, from h agteb,
  linarith,
end

example (h : a ≤ b) (h' : f b < f a) : ¬ monotone f :=
begin
  intros monotonef,
  have : f a ≤ f b, from monotonef h,
  linarith,
end

-- def monotone (f : α → β) : Prop := ∀ ⦃a b⦄, a ≤ b → f a ≤ f b
example :
  ¬ ∀ {f : ℝ → ℝ}, monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
begin
  intro h,
  let f := λ x : ℝ, (0 : ℝ),
  have monof : monotone f,
  -- 다른 사람 과제 확인해보자
  { intros z zz zltezz, refl, },
  have h' : f 1 ≤ f 0,
    from le_refl _,
  -- cases (h monof) with z zzz,
  have h₁ : ∀ {a b}, f a ≤ f b → a ≤ b , begin
    intros a b,
    apply h monof,
  end,
  have h'' : (1: ℝ) ≤ (0: ℝ), begin
    apply h₁ h',
  end,
  linarith,
end

example (x: ℝ) (h : 0 < x) : ∃ y, 0 < y ∧  y < x := begin
exact exists_between h,
-- exact Exists.intro 0 h,
-- sorry,
end

-- 다른사람들 과제 보자
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 :=
begin
  apply le_of_not_gt,
  intros xgt0,
  let half := λ z : ℝ, (z / 2),
  have h₁ : half x < x, begin
    exact half_lt_self xgt0,
  end,  
  have h₂ : 0 < half x, begin
    exact half_pos xgt0,
  end,
  have h₃ : x < half x, begin
    apply h (half x) h₂,
  end,
  linarith,
end

end

section
variables {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬ ∃ x, P x) : ∀ x, ¬ P x :=
begin
  intros x px,
  have h' : ∃ (x : α), P x, begin
    use x,
    exact px,
  end,
  exact h h',
end

example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x :=
begin
  intros existpx,
  cases existpx with x px,
  exact (h x px),
end

example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
begin
  -- have hnot : ∀ x, P x, sorry, 
  -- exact h hnot,
  -- intros existnpx,
sorry
end

example (h : ∃ x, ¬ P x) : ¬ ∀ x, P x :=
begin
  intros allpx,
  cases h with x npx,
  exact npx (allpx x),
end

open_locale classical

example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
begin
  by_contradiction h',
  apply h,
  intro x,
  show P x,
  by_contradiction h'',
  exact h' ⟨x, h''⟩
end

example (h : ¬ ¬ Q) : Q := begin
  by_contradiction h',
  exact h h',
end

example (h : Q) : ¬ ¬ Q :=
begin
  by_contradiction h',
  exact h' h,
end

end

open_locale classical
section
variable (f : ℝ → ℝ)

-- def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a := begin
  intros a,
  by_contradiction h',
  -- push_neg 안쓰고 어떻게 함?
  push_neg at h',
  have h₁ : fn_ub f a, from h',
  have h₂ : fn_has_ub f, from ⟨a, h₁⟩ ,
  exact h h₂,
end

example (h : ¬ ∀ a, ∃ x, f x > a) : fn_has_ub f :=
begin
  push_neg at h,
  exact h
end

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  simp only [fn_has_ub, fn_ub] at h,
  push_neg at h,
  exact h
end

example (h : ¬ monotone f) : ∃ x y, x ≤ y ∧ f y < f x :=
begin
  simp only [monotone] at h,
  push_neg at h,
  exact h,
end

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  contrapose! h,
  exact h
end

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 :=
begin
  contrapose! h,
  use x / 2,
  split; linarith
end

end

section
variable a : ℕ

example (h : 0 < 0) : a > 37 :=
begin
  exfalso,
  apply lt_irrefl 0 h
end

example (h : 0 < 0) : a > 37 :=
absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 :=
begin
  have h' : ¬ 0 < 0,
    from lt_irrefl 0,
  contradiction
end

end


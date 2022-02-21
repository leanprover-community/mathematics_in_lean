import data.real.basic

section
variables a b : ℝ

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a
def fn_has_lb (f : ℝ → ℝ) := ∃ a, fn_lb f a

variable f : ℝ → ℝ

example (h : ∀ a, ∃ x, f x < a) : ¬ fn_has_lb f :=
begin
  rintros ⟨a, ha⟩,
  rcases h a with ⟨x, hx⟩,
  have := ha x,
  linarith
end

example : ¬ fn_has_ub (λ x, x) :=
begin
  rintros ⟨a, ha⟩,
  have : a + 1 ≤ a := ha (a + 1),
  linarith
end

example (h : monotone f) (h' : f a < f b) : a < b :=
begin
  apply lt_of_not_ge,
  intro h'',
  apply absurd h',
  apply not_lt_of_ge (h h'')
end

example (h : a ≤ b) (h' : f b < f a) : ¬ monotone f :=
begin
  intro h'',
  apply absurd h',
  apply not_lt_of_ge,
  apply h'' h
end

example :
  ¬ ∀ {f : ℝ → ℝ}, monotone f → ∀ {a b}, f a ≤ f b → a ≤ b :=
begin
  intro h,
  let f := λ x : ℝ, (0 : ℝ),
  have monof : monotone f,
  { intros a b leab,
    refl },
  have h' : f 1 ≤ f 0,
    from le_refl _,
  have : (1 : ℝ) ≤ 0 := h monof h',
  linarith
end

example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 :=
begin
  apply le_of_not_gt,
  intro h',
  linarith [h _ h']
end

end

section
variables {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬ ∃ x, P x) : ∀ x, ¬ P x :=
begin
  intros x Px,
  apply h,
  use [x, Px]
end

example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x :=
begin
  rintros ⟨x, Px⟩,
  exact h x Px
end

example (h : ∃ x, ¬ P x) : ¬ ∀ x, P x :=
begin
  intro h',
  rcases h with ⟨x, nPx⟩,
  apply nPx,
  apply h'
end


example (h : ¬ ¬ Q) : Q :=
begin
  by_contradiction h',
  exact h h'
end

example (h : Q) : ¬ ¬ Q :=
begin
  intro h',
  exact h' h
end

end

open_locale classical
section
variable (f : ℝ → ℝ)

example (h : ¬ fn_has_ub f) : ∀ a, ∃ x, f x > a :=
begin
  intro a,
  by_contradiction h',
  apply h,
  use a,
  intro x,
  apply le_of_not_gt,
  intro h'',
  apply h',
  use [x, h'']
end

example (h : ¬ monotone f) : ∃ x y, x ≤ y ∧ f y < f x :=
begin
  rw [monotone] at h,
  push_neg at h,
  exact h
end

end


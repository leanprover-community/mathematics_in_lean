import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

section
variables (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : fn_lb f a) (hgb : fn_lb g b) :
  fn_lb (λ x, f x + g x) (a + b) :=
begin
  intro x,
  apply add_le_add,
  apply hfa,
  apply hgb
end

example (nnf : fn_lb f 0) (nng : fn_lb g 0) :
  fn_lb (λ x, f x * g x) 0 :=
begin
  intro x,
  apply mul_nonneg,
  apply nnf,
  apply nng
end

example (hfa : fn_ub f a) (hfb : fn_ub g b)
    (nng : fn_lb g 0) (nna : 0 ≤ a) :
  fn_ub (λ x, f x * g x) (a * b) :=
begin
  intro x,
  apply mul_le_mul,
  apply hfa,
  apply hfb,
  apply nng,
  apply nna
end

end

section
variables (f g : ℝ → ℝ)

example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) :=
begin
  intros a b aleb,
  apply mul_le_mul_of_nonneg_left _ nnc,
  apply mf aleb
end

example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) :=
λ a b aleb, mul_le_mul_of_nonneg_left (mf aleb) nnc

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
begin
  intros a b aleb,
  apply mf,
  apply mg,
  apply aleb
end

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
λ a b aleb, mf (mg aleb)

def fn_even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def fn_odd (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

example (of : fn_odd f) (og : fn_odd g) : fn_even (λ x, f x * g x) :=
begin
  intro x,
  calc
    (λ x, f x * g x) x = f x * g x          : rfl
                    ... = f (- x) * g (- x) : by rw [of, og, neg_mul_neg]
end

example (ef : fn_even f) (og : fn_odd g) : fn_odd (λ x, f x * g x) :=
begin
  intro x,
  dsimp,
  rw [ef, og, neg_mul_eq_mul_neg]
end

example (ef : fn_even f) (og : fn_odd g) : fn_even (λ x, f (g x)) :=
begin
  intro x,
  dsimp,
  rw [og, ←ef]
end

end

section
variables {α : Type*} (r s t : set α)

example : r ⊆ s → s ⊆ t → r ⊆ t :=
begin
  intros rsubs ssubt x xr,
  apply ssubt,
  apply rsubs,
  apply xr
end

theorem subset.trans : r ⊆ s → s ⊆ t → r ⊆ t :=
λ rsubs ssubt x xr, ssubt (rsubs xr)

end

section

variables {α : Type*} [partial_order α]
variables (s : set α) (a b : α)

def set_ub (s : set α) (a : α) := ∀ x, x ∈ s → x ≤ a

example (h : set_ub s a) (h' : a ≤ b) : set_ub s b :=
begin
  intros x xs,
  apply le_trans (h x xs) h'
end

example (h : set_ub s a) (h' : a ≤ b) : set_ub s b :=
λ x xs, le_trans (h x xs) h'

end

section
open function

example {c : ℝ} (h : c ≠ 0) : injective (λ x, c * x) :=
begin
  intros x₁ x₂ h',
  apply (mul_right_inj' h).mp h'
end

variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

example (injg : injective g) (injf : injective f) :
  injective (λ x, g (f x)) :=
begin
  intros x₁ x₂ h,
  apply injf,
  apply injg,
  apply h
end

end

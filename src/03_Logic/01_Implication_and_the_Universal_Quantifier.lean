import data.real.basic

#check ∀ x : ℝ, 0 ≤ x → abs x = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε

example : ∀ x y ε : ℝ, 0 < x → x < 1 → 0 < y → x * y ≤ 1:= begin
intro h,
intro i,
intro j,
intro k,
intro l,
intro m,
suggest,
  
  -- ring,
  sorry,
end

lemma my_lemma : ∀ x y ε : ℝ,
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε := begin
  intro x,
  intro y,
  intro ε,
  intro h,
  intro i,
  intro j,
  intro k,
  -- assume h : 0 < ε,
sorry,
end

section
  variables a b δ : ℝ
  variables (h₀ : 0 < δ) (h₁ : δ ≤ 1)
  variables (ha : abs a < δ) (hb : abs b < δ)

  #check my_lemma a b δ
  #check my_lemma a b δ h₀ h₁
  #check my_lemma a b δ h₀ h₁ ha hb
end

lemma my_lemma2 : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
sorry

section
  variables a b δ : ℝ
  variables (h₀ : 0 < δ) (h₁ : δ ≤ 1)
  variables (ha : abs a < δ) (hb : abs b < δ)

  #check my_lemma2 h₀ h₁ ha hb
end

lemma my_lemma3 : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
begin
  intros x y ε epos ele1 xlt ylt,
  sorry
end

#check abs_mul -- abs_mul : ∀ (a b : ?M_1), |a * b| = |a| * |b|
#check mul_le_mul -- a ≤ c → b ≤ d → 0 ≤ b → 0 ≤ c → a * b ≤ c * d 
#check abs_nonneg -- (a : α) : 0 ≤ |a| 
#check mul_lt_mul_right -- (h : 0 < c) : a * c < b * c ↔ a < b 
#check one_mul --  ∀ a : M, 1 * a = a 

lemma my_lemma4 : ∀ {x y ε : ℝ},
  0 < ε → ε ≤ 1 → abs x < ε → abs y < ε → abs (x * y) < ε :=
begin
  intros x y ε epos ele1 xlt ylt,
  calc
    abs (x * y) = abs x * abs y : by rw abs_mul
    ... ≤ abs x * ε             : 
    begin
      apply mul_le_mul,
      { show |x| ≤ |x|, refl},
      { show |y| ≤ ε, exact le_of_lt ylt},
      { show 0 ≤ |y|, exact abs_nonneg y},
      { show 0 ≤ |x|, exact abs_nonneg x },
    end
    ... < 1 * ε                 : begin
    have h₀ : abs x < 1, begin
      apply lt_of_lt_of_le,
      { show |x| < ε, exact xlt },
      { show ε ≤ 1, exact ele1 },
    end,
    have h₁ : abs x * ε < 1 * ε, by apply ((mul_lt_mul_right epos).mpr h₀),
    exact h₁,
    end
    ... = ε                     : by apply one_mul,

end

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_lb (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, a ≤ f x

section
variables (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : fn_ub f a) (hgb : fn_ub g b) :
  fn_ub (λ x, f x + g x) (a + b) :=
begin
  intro x,
  -- dsimp,
  change f x + g x ≤ a + b, 
  apply add_le_add,
  apply hfa,
  apply hgb
end

example (hfa : fn_lb f a) (hgb : fn_lb g b) :
  fn_lb (λ x, f x + g x) (a + b) := begin
  intro x,
  change a + b ≤ f x + g x,
  apply add_le_add,
  apply hfa,
  apply hgb,
end

example (nnf : fn_lb f 0) (nng : fn_lb g 0) :
  fn_lb (λ x, f x * g x) 0 := begin
  intro x,
  change 0 ≤ f x * g x,
  apply mul_nonneg,
  apply nnf,
  apply nng,
end

example (hfa : fn_ub f a) (hfb : fn_ub g b)
    (nng : fn_lb g 0) (nna : 0 ≤ a) :
  fn_ub (λ x, f x * g x) (a * b) := begin
  intro x,
  change f x * g x ≤ a * b,
  apply mul_le_mul,
  apply hfa,
  apply hfb,
  apply nng,
  apply nna,
end

end

section
variables {α : Type*} {R : Type*} [ordered_cancel_add_comm_monoid R]

#check @add_le_add

def fn_ub' (f : α → R) (a : R) : Prop := ∀ x, f x ≤ a

theorem fn_ub_add {f g : α → R} {a b : R}
    (hfa : fn_ub' f a) (hgb : fn_ub' g b) :
  fn_ub' (λ x, f x + g x) (a + b) :=
λ x, add_le_add (hfa x) (hgb x)
end

example (f : ℝ → ℝ) (h : monotone f) :
  ∀ {a b}, a ≤ b → f a ≤ f b := h

section
variables (f g : ℝ → ℝ)

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
begin
  intros a b aleb,
  apply add_le_add,
  apply mf aleb,
  apply mg aleb
end

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
λ a b aleb, add_le_add (mf aleb) (mg aleb)

example {c : ℝ} (mf : monotone f) (nnc : 0 ≤ c) :
  monotone (λ x, c * f x) := 
  λ a b aleb, mul_le_mul_of_nonneg_left (mf aleb) nnc

example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f (g x)) :=
  λ a b aleb, mf (mg aleb)

def fn_even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def fn_odd (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

example (ef : fn_even f) (eg : fn_even g) : fn_even (λ x, f x + g x) :=
begin
  intro x,
  calc
    (λ x, f x + g x) x = f x + g x       : rfl
                    ... = f (-x) + g (-x) : by rw [ef, eg]
end

example (of : fn_odd f) (og : fn_odd g) : fn_even (λ x, f x * g x) :=
begin
  intro x,
  calc
    (λ x, f x * g x) x = f x * g x : rfl
       ... = (-f (-x)) * (-g (-x)) : by rw [of, og]
       ... = f (-x) * g (-x) : by ring
end

example (ef : fn_even f) (og : fn_odd g) : fn_odd (λ x, f x * g x) :=
begin
  intro x,
  calc
    (λ x, f x * g x) x = f x * g x : rfl
      ... = f (-x) * (-g (-x)) : by rw [ef, og]
      ... = - (f (-x) * g (-x)) : by ring
end

example (ef : fn_even f) (og : fn_odd g) : fn_even (λ x, f (g x)) :=
begin
  intro x,
  calc
    (λ x, f (g x)) x = f (g x) : rfl 
    ... = f (- (-g (-x))) : by rw [ef, og]
    ... = f (g (-x)) : by ring
end

end

section
variables {α : Type*} (r s t : set α)

example : s ⊆ s :=
by { intros x xs, exact xs }

theorem subset.refl : s ⊆ s := λ x xs, xs

theorem subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := begin
  intros rss sst,
  have h₀ : (∀ x : α, x ∈ r → x ∈ s), by apply rss,
  have h₁ : (∀ x : α, x ∈ s → x ∈ t), by apply sst,
  have h₂ : (∀ x : α, x ∈ r → x ∈ t), begin 
    intros x xinr,
    apply h₁,
    apply h₀,
    apply xinr,
  end,
  exact h₂,
end

end

section

variables {α : Type*} [partial_order α]
variables (s : set α) (a b : α)

def set_ub (s : set α) (a : α) := ∀ x, x ∈ s → x ≤ a

example (h : set_ub s a) (h' : a ≤ b) : set_ub s b := begin
  intros x xins,
  have h₀ : x ≤ a, begin apply h _ xins end,
  have h₁ : x ≤ b, begin apply le_trans h₀ h' end,
  exact h₁,
end

end

section
open function

example (c : ℝ) : injective (λ x, x + c) :=
begin
  intros x₁ x₂ h',
  exact (add_left_inj c).mp h',
end

example { c x y : ℝ } (h : c ≠ 0) : c * x = c * y → x = y := begin
  exact (mul_right_inj' h).mp,
end 

#check mul_right_inj -- (a : G) {b c : G} : a * b = a * c ↔ b = c  
#check mul_right_inj' -- (ha : a ≠ 0) : a * b = a * c ↔ b = c

example {c : ℝ} (h : c ≠ 0) : injective (λ x, c * x) := begin
  intros x₁ x₂ h₁,
  change c * x₁ = c * x₂ at h₁,
  apply (mul_right_inj' h).mp h₁,
end

variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

-- injective (f : α → β) := ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
example (injg : injective g) (injf : injective f) :
  injective (λ x, g (f x)) := begin
  intros x y h,
  change g (f x) = g (f y) at h,

  have h₀ : f x = f y, by exact injg h,
  have h₁ : x = y, by exact injf h₀,
  exact h₁,
end

end

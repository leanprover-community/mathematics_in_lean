import data.set.lattice
import data.set.function
import analysis.special_functions.log.basic

section

variables {α β : Type*}
variable  f : α → β
variables s t : set α
variables u v : set β
open function
open set

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v :=
begin
  split,
  { intros h x xs,
    have : f x ∈ f '' s,
    from mem_image_of_mem _ xs,
    exact h this },
  intros h y ymem,
  rcases ymem with ⟨x, xs, fxeq⟩,
  rw ← fxeq,
  apply h xs
end

example (h : injective f) : f ⁻¹' (f '' s) ⊆ s :=
begin
  rintros x ⟨y, ys, fxeq⟩,
  rw ← h fxeq,
  exact ys
end

example : f '' (f⁻¹' u) ⊆ u :=
begin
  rintros y ⟨x, xmem, rfl⟩,
  exact xmem
end

example (h : surjective f) : u ⊆ f '' (f⁻¹' u) :=
begin
  intros y yu,
  rcases h y with ⟨x, fxeq⟩,
  use x,
  split,
  { show f x ∈ u,
    rw fxeq, exact yu },
  exact fxeq
end

example (h : s ⊆ t) : f '' s ⊆ f '' t :=
begin
  rintros y ⟨x, xs, fxeq⟩,
  use [x, h xs, fxeq]
end

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v :=
by intro x; apply h

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v :=
by ext x; refl

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
begin
  rintros y ⟨x, ⟨xs, xt⟩, rfl⟩,
  use [x, xs, rfl, x, xt, rfl]
end

example (h : injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) :=
begin
  rintros y ⟨⟨x₁, x₁s, rfl⟩, ⟨x₂, x₂t, fx₂eq⟩⟩,
  use [x₁, x₁s],
  rw ← h fx₂eq,
  exact x₂t
end

example : f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  rintros y ⟨⟨x₁, x₁s, rfl⟩, h⟩,
  use [x₁, x₁s],
  intro h',
  apply h,
  use [x₁, h', rfl]
end

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) :=
λ x, id

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) :=
begin
  ext y, split,
  { rintros ⟨⟨x, xs, rfl⟩, fxv⟩,
    use [x, xs, fxv] },
  rintros ⟨x, ⟨⟨xs, fxv⟩, rfl⟩⟩,
  use [x, xs, rfl, fxv],
end

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u :=
begin
  rintros y ⟨x, ⟨xs, fxu⟩, rfl⟩,
  use [x, xs, rfl, fxu],
end

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) :=
begin
  rintros x ⟨xs, fxu⟩,
  use [x, xs, rfl, fxu],
end

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) :=
begin
  rintros x (xs | fxu),
  { left, use [x, xs, rfl] },
  right, use fxu
end

variables {I : Type*} (A : I → set α) (B : I → set β)

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
begin
  ext y, simp,
  split,
  { rintros ⟨x, ⟨i, xAi⟩, fxeq⟩,
    use [i, x, xAi, fxeq] },
  rintros ⟨i, x, xAi, fxeq⟩,
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩
end

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
begin
  intro y, simp,
  intros x h fxeq i,
  use [x, h i, fxeq],
end

example (i : I) (injf : injective f) : (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
begin
  intro y, simp,
  intro h,
  rcases h i with ⟨x, xAi, fxeq⟩,
  use x, split,
  { intro i',
    rcases h i' with ⟨x', x'Ai, fx'eq⟩,
    have : f x = f x', by rw [fxeq, fx'eq],
    have : x = x', from injf this,
    rw this,
    exact x'Ai },
  exact fxeq
end

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
by { ext x, simp }

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
by { ext x, simp }

end

section
open set real

example : inj_on sqrt { x | x ≥ 0 } :=
begin
  intros x xnonneg y ynonneg,
  intro e,
  calc
    x   = (sqrt x)^2 : by rw sq_sqrt xnonneg
    ... = (sqrt y)^2 : by rw e
    ... = y          : by rw sq_sqrt ynonneg
end

example : inj_on (λ x, x^2) { x : ℝ | x ≥ 0 } :=
begin
    intros x xnonneg y ynonneg,
    intro e,
    dsimp at *,
    calc
      x   = sqrt (x^2) : by rw sqrt_sq xnonneg
      ... = sqrt (y^2) : by rw e
      ... = y          : by rw sqrt_sq ynonneg,
end

example : sqrt '' { x | x ≥ 0 } = {y | y ≥ 0} :=
begin
    ext y, split,
    { rintros ⟨x, ⟨xnonneg, rfl⟩⟩,
      apply sqrt_nonneg },
    intro ynonneg,
    use y^2,
    dsimp at *,
    split,
    apply pow_nonneg ynonneg,
    apply sqrt_sq,
    assumption,
end

example : range (λ x, x^2) = {y : ℝ | y ≥ 0} :=
begin
    ext y,
    split,
    { rintros ⟨x, rfl⟩,
       dsimp at *,
       apply pow_two_nonneg },
    intro ynonneg,
    use sqrt y,
    exact sq_sqrt ynonneg,
end

end

section
variables {α β : Type*} [inhabited α]

noncomputable theory
open_locale classical

def inverse (f : α → β) : β → α :=
λ y : β, if h : ∃ x, f x = y then classical.some h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) :
  f (inverse f y) = y :=
begin
  rw inverse, dsimp, rw dif_pos h,
  exact classical.some_spec h
end

variable  f : α → β
open function

example : injective f ↔ left_inverse (inverse f) f  :=
begin
  split,
  { intros h y,
    apply h,
    apply inverse_spec,
    use y },
  intros h x1 x2 e,
  rw [←h x1, ←h x2, e]
end

example : injective f ↔ left_inverse (inverse f) f  :=
⟨λ h y, h (inverse_spec _ ⟨y, rfl⟩), λ h x1 x2 e, by rw [←h x1, ←h x2, e]⟩

example : surjective f ↔ right_inverse (inverse f) f :=
begin
  split,
  { intros h y,
    apply inverse_spec,
    apply h },
  intros h y,
  use (inverse f y),
  apply h
end

example : surjective f ↔ right_inverse (inverse f) f :=
⟨λ h y, inverse_spec _ (h _), λ h y, ⟨inverse f y, h _⟩⟩

end

section
variable {α : Type*}
open function

theorem Cantor : ∀ f : α → set α, ¬ surjective f :=
begin
  intros f surjf,
  let S := { i | i ∉ f i},
  rcases surjf S with ⟨j, h⟩,
  have h₁ : j ∉ f j,
  { intro h',
    have : j ∉ f j,
      by rwa h at h',
    contradiction },
  have h₂ : j ∈ S,
    from h₁,
  have h₃ : j ∉ S,
    by rwa h at h₁,
  contradiction
end

end

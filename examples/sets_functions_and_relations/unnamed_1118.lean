import data.set.function

open set

variables {α β : Type*}
variables (f : α → β) (s : set α)

-- BEGIN
example : inj_on f s ↔
  ∀ {x₁ x₂}, x₁ ∈ s → x₂ ∈ s → f x₁ = f x₂ → x₁ = x₂ :=
iff.refl _
-- END
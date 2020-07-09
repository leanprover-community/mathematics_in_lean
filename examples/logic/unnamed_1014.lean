import tactic

open function

variables {α : Type*} {β : Type*} {γ : Type*}
variables {g : β → γ} {f : α → β}

-- BEGIN
example (surjg : surjective g) (surjf : surjective f) :
  surjective (λ x, g (f x)) :=
sorry
-- END
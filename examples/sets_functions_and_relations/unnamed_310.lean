import data.set.basic

variable {α : Type*}
variables (s t u : set α)

-- BEGIN
example : s ∩ t = t ∩ s :=
set.ext $ λ x, ⟨λ ⟨xs, xt⟩, ⟨xt, xs⟩, λ ⟨xt, xs⟩, ⟨xs, xt⟩⟩
-- END
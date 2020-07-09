import data.set.function

variables {α β : Type*}
variable  f : α → β
variables (s : set α) (t : set β)

-- BEGIN
example : f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
sorry
-- END
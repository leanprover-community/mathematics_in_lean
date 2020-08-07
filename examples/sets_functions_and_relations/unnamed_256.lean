import tactic

variable {α : Type*}
variables (s t u : set α)

-- BEGIN
example : s \ (t ∪ u) ⊆ s \ t \ u :=
sorry
-- END
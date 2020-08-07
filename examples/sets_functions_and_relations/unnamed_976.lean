import data.set.lattice

open set function

-- BEGIN
variables {α β I : Type*}
variable  f : α → β
variable  A : I → set α
variable  B : I → set β

example : f '' (⋃ i, A i) = ⋃ i, f '' A i :=
sorry

example : f '' (⋂ i, A i) ⊆ ⋂ i, f '' A i :=
sorry

example (i : I) (injf : injective f) :
  (⋂ i, f '' A i) ⊆ f '' (⋂ i, A i) :=
sorry

example : f ⁻¹' (⋃ i, B i) = ⋃ i, f ⁻¹' (B i) :=
sorry

example : f ⁻¹' (⋂ i, B i) = ⋂ i, f ⁻¹' (B i) :=
sorry
-- END
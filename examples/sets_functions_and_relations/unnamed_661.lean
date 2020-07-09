import tactic

open set

variables α I : Type*
variable  A : I → set α
variable  s : set α

-- BEGIN
open_locale classical

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
sorry
-- END
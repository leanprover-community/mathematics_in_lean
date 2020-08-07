import data.set.basic

open set

variable {α : Type*}
variables (s t u : set α)

-- BEGIN
example : s ∩ t = t ∩ s :=
subset.antisymm sorry sorry
-- END
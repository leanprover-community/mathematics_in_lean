import tactic

variable {α : Type*}
variables (s t u : set α)

-- BEGIN
example : s ∩ t = t ∩ s :=
by ext x; simp [and.comm]
-- END
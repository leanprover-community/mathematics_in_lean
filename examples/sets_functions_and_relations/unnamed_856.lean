import data.set.function

variables {α β : Type*}
variable  f : α → β
variables s t : set α

-- BEGIN
example : s ⊆ f ⁻¹' (f '' s) :=
begin
  intros x xs,
  show f x ∈ f '' s,
  use [x, xs]
end
-- END
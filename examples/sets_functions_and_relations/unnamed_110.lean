variable {α : Type*}
variables (s t u : set α)

-- BEGIN
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
begin
  intros x xsu,
  exact ⟨h xsu.1, xsu.2⟩
end
-- END
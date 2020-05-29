variables {α : Type*} (P : α → Prop)

example (h : ¬ ∃ x, P x) : ∀ x, ¬ P x :=
sorry

example (h : ∀ x, ¬ P x) : ¬ ∃ x, P x :=
sorry

example (h : ¬ ∀ x, P x) : ∃ x, ¬ P x :=
sorry

example (h : ∃ x, ¬ P x) : ¬ ∀ x, P x :=
sorry
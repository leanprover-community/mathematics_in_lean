variables {α : Type*} (r s t : set α)

example : s ⊆ s :=
by { intros x xs, exact xs }

theorem subset.refl : s ⊆ s := λ x xs, xs

example : r ⊆ s → s ⊆ t → r ⊆ t :=
begin
  sorry
end

theorem subset.trans : r ⊆ s → s ⊆ t → r ⊆ t :=
sorry
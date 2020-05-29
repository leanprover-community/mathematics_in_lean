variables {α : Type*} (r s t : set α)

example : s ⊆ s :=
by { intros x xs, exact xs }

example : s ⊆ s := λ x xs, xs

example : r ⊆ s → s ⊆ t → r ⊆ t :=
begin
  sorry
end

example : r ⊆ s → s ⊆ t → r ⊆ t :=
sorry
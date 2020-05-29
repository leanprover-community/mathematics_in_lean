import data.real.basic

variables (f g : ℝ → ℝ)

-- BEGIN
def even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def odd (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

example (ef : even f) (eg : even g) : even (λ x, f x + g x) :=
begin
  intro x,
  calc
    (λ x, f x + g x) x = f x + g x       : rfl
                   ... = f (-x) + g (-x) : by rw [ef, eg]
end

example (of : odd f) (og : odd g) : even (λ x, f x * g x) :=
sorry

example (ef : even f) (og : odd g) : odd (λ x, f x * g x) :=
sorry

example (ef : even f) (og : odd g) : even (λ x, f (g x)) :=
sorry
-- END
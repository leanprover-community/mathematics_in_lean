import data.real.basic

variables (f g : ℝ → ℝ)

-- BEGIN
def fn_even (f : ℝ → ℝ) : Prop := ∀ x, f x = f (-x)
def fn_odd (f : ℝ → ℝ) : Prop := ∀ x, f x = - f (-x)

example (ef : fn_even f) (eg : fn_even g) : fn_even (λ x, f x + g x) :=
begin
  intro x,
  calc
    (λ x, f x + g x) x = f x + g x       : rfl
                   ... = f (-x) + g (-x) : by rw [ef, eg]
end

example (of : fn_odd f) (og : fn_odd g) : fn_even (λ x, f x * g x) :=
sorry

example (ef : fn_even f) (og : fn_odd g) : fn_odd (λ x, f x * g x) :=
sorry

example (ef : fn_even f) (og : fn_odd g) : fn_even (λ x, f (g x)) :=
sorry
-- END
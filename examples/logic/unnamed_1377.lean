import data.real.basic

def fn_ub (f : ℝ → ℝ) (a : ℝ) : Prop := ∀ x, f x ≤ a
def fn_has_ub (f : ℝ → ℝ) := ∃ a, fn_ub f a

open_locale classical

variable (f : ℝ → ℝ)

-- BEGIN
example (h : ¬ monotone f) : ∃ x y, x ≤ y ∧ f y < f x :=
sorry
-- END
import data.real.basic

-- BEGIN
open function

example (c : ℝ) : injective (λ x, x + c) :=
begin
  intros x₁ x₂ h',
  apply eq_of_add_eq_add_right h',
end

example {c : ℝ} (h : c ≠ 0) : injective (λ x, c * x) :=
sorry
-- END
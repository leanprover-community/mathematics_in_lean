import data.real.basic

variables {x y : ℝ}

namespace my_abs

-- BEGIN
theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
sorry

theorem abs_lt : abs x < y ↔ - y < x ∧ x < y :=
sorry
-- END

end my_abs
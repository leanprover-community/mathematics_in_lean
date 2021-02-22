import analysis.special_functions.exp_log

open real

-- BEGIN
example (a b : ℝ) (h : a ≤ b) : exp a ≤ exp b :=
begin
  rw exp_le_exp,
  exact h
end
-- END
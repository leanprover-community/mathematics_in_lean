import analysis.special_functions.exp_log

open real

variables a b c : ℝ

-- BEGIN
example (h : 1 ≤ a) (h' : b ≤ c) :
  2 + a + exp b ≤ 3 * a + exp c :=
by linarith [exp_le_exp.mpr h']
-- END
import data.real.basic

variables (f : ℝ → ℝ) (a b : ℝ)

-- BEGIN
example (h : monotone f) (h' : f a < f b) : a < b :=
sorry

example (h : a ≤ b) (h' : f b < f a) : ¬ monotone f :=
sorry
-- END
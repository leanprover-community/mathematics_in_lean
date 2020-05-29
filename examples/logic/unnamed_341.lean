import data.real.basic

variables (f g : ℝ → ℝ)

-- BEGIN
example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
λ a b aleb, add_le_add (mf aleb) (mg aleb)
-- END
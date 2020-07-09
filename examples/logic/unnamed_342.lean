import data.real.basic

variables (f g : ℝ → ℝ)

-- BEGIN
example (mf : monotone f) (mg : monotone g) :
  monotone (λ x, f x + g x) :=
begin
  intros a b aleb,
  apply add_le_add,
  apply mf aleb,
  apply mg aleb
end
-- END
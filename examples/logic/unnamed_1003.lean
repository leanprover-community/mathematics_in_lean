import data.real.basic

variables a b : ℝ

-- BEGIN
example (h : a < b) : ¬ b < a :=
begin
  intro h',
  have : a < a,
    from lt_trans h h',
  apply lt_irrefl a this
end
-- END
import data.real.basic

variables a b : ℝ

-- BEGIN
example : min a b = min b a :=
begin
  apply le_antisymm,
  repeat {
    apply le_min,
    apply min_le_right,
    apply min_le_left }
end
-- END
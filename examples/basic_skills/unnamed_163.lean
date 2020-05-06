import data.real.basic

-- BEGIN
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) :
  a * (b * e) = c * (d * f) :=
begin
  rw h',
  rw ←mul_assoc,
  rw h,
  rw mul_assoc
end
-- END
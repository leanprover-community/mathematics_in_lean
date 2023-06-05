import data.real.basic

example (a b c : ℝ) : (c * b) * a = b * (a * c) :=
begin
  rw mul_comm c b,
  rw mul_assoc b c a,
  rw mul_comm c a
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw ←mul_assoc a b c,
  rw mul_comm a b,
  rw mul_assoc b a c
end

example (a b c : ℝ) : a * (b * c) = b * (c * a) :=
begin
  rw mul_comm,
  rw mul_assoc
end

example (a b c : ℝ) : a * (b * c) = b * (a * c) :=
begin
  rw ←mul_assoc,
  rw mul_comm a,
  rw mul_assoc
end

example (a b c d e f : ℝ) (h : b * c = e * f) :
  a * b * c * d = a * e * f * d :=
begin
  rw mul_assoc a,
  rw h,
  rw ←mul_assoc
end

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 :=
begin
  rw hyp,
  rw hyp',
  rw mul_comm,
  rw sub_self
end


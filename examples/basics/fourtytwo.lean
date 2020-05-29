  import data.real.basic

  example (a b c : ℝ) : (a * b) * c = b * (a * c) :=
  begin
    rw mul_comm a b,
    rw mul_assoc b a c
  end
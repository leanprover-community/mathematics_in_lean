import data.real.basic

variable {y : ℝ}

-- BEGIN
example (h : y > 0) : y > 0 ∨ y < -1 :=
or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
or.inr h
-- END
import algebra.ordered_ring

variables {R : Type*} [ordered_ring R]
variables a b c : R

-- BEGIN
example : a ≤ b → 0 ≤ b - a := sorry

example : 0 ≤ b - a → a ≤ b := sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := sorry
-- END
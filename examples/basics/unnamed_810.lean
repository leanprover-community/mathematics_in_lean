import algebra.ring

variables {R : Type*} [ring R]

-- BEGIN
example (a b : R) : a - b = a + -b :=
sub_eq_add_neg a b
-- END
namespace my_ring

variables {R : Type*} [ring R]

-- BEGIN
theorem sub_eq_add_neg (a b : R) : a - b = a + -b :=
rfl

example (a b : R) : a - b = a + -b :=
by reflexivity
-- END

end my_ring
namespace my_ring

variables {R : Type*} [ring R]

-- BEGIN
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b :=
by rw [←add_assoc, add_left_neg, zero_add]
-- END

end my_ring
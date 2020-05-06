namespace my_ring

variables {R : Type*} [ring R]

-- BEGIN
lemma one_add_one_eq_two : 1 + 1 = (2 : R) :=
by refl

theorem two_mul (a : R) : 2 * a = a + a :=
sorry
-- END

end my_ring
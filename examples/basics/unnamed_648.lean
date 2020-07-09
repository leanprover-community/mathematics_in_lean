import algebra.ring

namespace my_ring

variables {R : Type*} [ring R]

-- BEGIN
theorem add_neg_cancel_right (a b : R) : (a + b) + -b = a :=
sorry
-- END

end my_ring
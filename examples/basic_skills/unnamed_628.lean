namespace my_ring

variables {R : Type*} [ring R]

-- BEGIN
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
sorry

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c :=
sorry
-- END

end my_ring
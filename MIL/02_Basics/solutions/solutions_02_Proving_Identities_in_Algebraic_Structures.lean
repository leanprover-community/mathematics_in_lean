import algebra.ring
import data.real.basic
import tactic

namespace my_ring
variables {R : Type*} [ring R]

theorem add_neg_cancel_right (a b : R) : (a + b) + -b = a :=
by rw [add_assoc, add_right_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c :=
by rw [←neg_add_cancel_left a b, h, neg_add_cancel_left]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c :=
by rw [←add_neg_cancel_right a b, h, add_neg_cancel_right]

theorem zero_mul (a : R) : 0 * a = 0 :=
begin
  have h : 0 * a + 0 * a = 0 * a + 0,
  { rw [←add_mul, add_zero, add_zero] },
  rw add_left_cancel h
end

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b :=
by rw [←neg_add_cancel_left a b, h, add_zero]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b :=
begin
  symmetry,
  apply neg_eq_of_add_eq_zero,
  rw [add_comm, h]
end

theorem neg_zero : (-0 : R) = 0 :=
begin
  apply neg_eq_of_add_eq_zero,
  rw add_zero
end

theorem neg_neg (a : R) : -(-a) = a :=
begin
  apply neg_eq_of_add_eq_zero,
  rw add_left_neg
end

end my_ring

namespace my_ring

variables {R : Type*} [ring R]

theorem self_sub (a : R) : a - a = 0 :=
by rw [sub_eq_add_neg, add_right_neg]

lemma one_add_one_eq_two : 1 + 1 = (2 : R) :=
by refl

theorem two_mul (a : R) : 2 * a = a + a :=
by rw [←one_add_one_eq_two, add_mul, one_mul]

end my_ring

section
variables {G : Type*} [group G]

namespace my_group

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 :=
begin
  have h : (a * a⁻¹)⁻¹ * ((a * a⁻¹) * (a * a⁻¹)) = 1,
  { rw [mul_assoc, ←mul_assoc a⁻¹ a, mul_left_inv, one_mul, mul_left_inv] },
  rw [←h, ←mul_assoc, mul_left_inv, one_mul]
end

theorem mul_one (a : G) : a * 1 = a :=
by rw [←mul_left_inv a, ←mul_assoc, mul_right_inv, one_mul]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a ⁻¹ :=
by rw [←one_mul (b⁻¹ * a⁻¹), ←mul_left_inv (a * b), mul_assoc, mul_assoc,
        ←mul_assoc b b⁻¹, mul_right_inv, one_mul, mul_right_inv, mul_one]

end my_group
end


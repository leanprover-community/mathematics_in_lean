module
public import MIL.Common
public import Mathlib.Basic.Real.Basic
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)


example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [add_mul, mul_add, mul_add, ← add_assoc]

example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  calc (a + b) * (c + d) = a*(c+d) + b*(c+d) := by rw [add_mul]
  _  = (a*c+a*d) + (b*c+b*d) := by rw [mul_add, mul_add]
  _ = a * c + a * d + b * c + b * d := by rw [← add_assoc]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [add_mul, mul_sub, mul_sub, add_sub, mul_comm b a,
      ← pow_two, ← pow_two, sub_add, sub_self, sub_zero]

end


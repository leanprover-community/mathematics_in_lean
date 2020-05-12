open nat

variables m n k : ℕ

namespace my_nat

-- BEGIN
theorem mul_add : m * (n + k) = m * n + m * k := sorry

theorem zero_mul : 0 * n = 0 := sorry

theorem one_mul : 1 * n = n := sorry

theorem mul_assoc : m * n * k = m * (n * k) := sorry

theorem mul_comm : m * n= n * m := sorry
-- END

end my_nat
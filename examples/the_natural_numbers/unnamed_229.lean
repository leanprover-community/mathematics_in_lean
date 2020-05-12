open nat

variables m n : ℕ

-- BEGIN
#check (mul_zero m   : m * 0 = 0)
#check (mul_succ m n : m * (succ n) = m * n + m)

example : m * 0 = 0 := rfl
example : m * (n + 1) = m * n + m := rfl
-- END
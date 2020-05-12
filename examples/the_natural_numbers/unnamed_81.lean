open nat

variables m n : ℕ

-- BEGIN
example : m + 0 = m := rfl
example : m + (succ n) = succ (m + n) := rfl
-- END
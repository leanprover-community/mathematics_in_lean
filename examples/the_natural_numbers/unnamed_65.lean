open nat

variables m n : ℕ

-- BEGIN
#check (add_zero m   : m + 0 = m)
#check (add_succ m n : m + (succ n) = succ (m + n))
-- END
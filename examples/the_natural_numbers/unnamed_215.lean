namespace my_nat

-- BEGIN
def mul : ℕ → ℕ → ℕ
| m 0     := 0
| m (n+1) := mul m n + m
-- END

end my_nat
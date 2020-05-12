open nat

namespace my_nat

-- BEGIN
def add : ℕ → ℕ → ℕ
| m 0 := m
| m (succ n) := succ (add m n)
-- END

end my_nat
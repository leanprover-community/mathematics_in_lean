open nat

variables m n k : ℕ

namespace my_nat

-- BEGIN
theorem add_assoc : m + n + k = m + (n + k) :=
begin
  induction k with k ih,
  { refl },
  rw [add_succ, ih],
  refl
end
-- END

end my_nat
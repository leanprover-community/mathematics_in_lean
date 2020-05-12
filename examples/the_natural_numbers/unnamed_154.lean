open nat

variables m n : ℕ

namespace my_nat

-- BEGIN
theorem zero_add : 0 + m = m :=
begin
  induction m with m ih,
  { refl },
  rw [add_succ, ih]
end

theorem succ_add : succ m + n = succ (m + n) :=
begin
  induction n with n ih,
  { refl },
  rw [add_succ, ih]
end

theorem add_comm : m + n = n + m :=
begin
  induction n with n ih,
  { rw zero_add, refl },
  rw [succ_add, ←ih]
end
-- END

end my_nat
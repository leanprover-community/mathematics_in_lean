import data.nat.parity tactic
open nat

-- BEGIN
example : ∀ m n, even n → even (m * n) :=
by rintros m n ⟨k, hk⟩; use m * k; rw [hk, mul_left_comm]
-- END
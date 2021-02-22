import data.nat.parity tactic
open nat

-- BEGIN
example : ∀ m n : nat, even n → even (m * n) :=
by { rintros m n ⟨k, hk⟩, use m * k, rw hk, ring }
-- END
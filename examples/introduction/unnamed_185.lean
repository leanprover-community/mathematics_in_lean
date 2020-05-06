import data.nat.parity tactic
open nat

example : ∀ m n, even n → even (m * n) :=
begin
  rintros m n ⟨k, hk⟩,
  use m * k,
  rw [hk, mul_left_comm]
end
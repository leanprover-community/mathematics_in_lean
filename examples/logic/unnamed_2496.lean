import data.real.basic

-- BEGIN
variables {α : Type*} [linear_order α]

def converges_to (s : α → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε
-- END
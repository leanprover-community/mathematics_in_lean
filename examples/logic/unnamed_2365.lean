import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
sorry

variables {s : ℕ → ℝ} {a : ℝ}

-- BEGIN
theorem converges_to_mul_const
    {c : ℝ} (cs : converges_to s a) :
  converges_to (λ n, c * s n) (c * a) :=
begin
  by_cases h : c = 0,
  { convert converges_to_const 0,
    { ext, rw [h, zero_mul] },
    rw [h, zero_mul] },
  have acpos : 0 < abs c,
    from abs_pos.mpr h,
  sorry
end
-- END
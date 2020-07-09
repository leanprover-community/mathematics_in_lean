import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
sorry

variables {s t : ℕ → ℝ} {a b : ℝ}

theorem converges_to_add
    (cs : converges_to s a) (ct : converges_to t b):
  converges_to (λ n, s n + t n) (a + b) :=
sorry

theorem converges_to_mul_const
    (c : ℝ) (cs : converges_to s a) :
  converges_to (λ n, c * s n) (c * a) :=
sorry

lemma aux (cs : converges_to s a) (ct : converges_to t 0) :
  converges_to (λ n, s n * t n) 0 :=
sorry

-- BEGIN
theorem converges_to_mul
    (cs : converges_to s a) (ct : converges_to t b):
  converges_to (λ n, s n * t n) (a * b) :=
begin
  have h₁ : converges_to (λ n, s n * (t n - b)) 0,
  { apply aux cs,
    convert converges_to_add ct (converges_to_const (-b)),
    ring },
  convert (converges_to_add h₁ (converges_to_mul_const b cs)),
  { ext, ring },
  ring
end
-- END
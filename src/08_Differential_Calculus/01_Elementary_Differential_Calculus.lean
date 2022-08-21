import analysis.special_functions.trigonometric.deriv
import analysis.calculus.mean_value

open set filter
open_locale topological_space filter classical real

noncomputable theory

open real

/-- The sin function has derivative 1 at 0. -/
example : has_deriv_at sin 1 0 :=
by simpa using has_deriv_at_sin 0

example (x : ℝ) : differentiable_at ℝ sin x :=
(has_deriv_at_sin x).differentiable_at

example {f : ℝ → ℝ} {x a : ℝ} (h : has_deriv_at f a x) : deriv f x = a :=
h.deriv

example {f : ℝ → ℝ} {x : ℝ} (h : ¬ differentiable_at ℝ f x) : deriv f x = 0 :=
deriv_zero_of_not_differentiable_at h

example {f g : ℝ → ℝ} {x : ℝ} (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x) :
  deriv (f + g) x = deriv f x + deriv g x :=
deriv_add hf hg

example {f : ℝ → ℝ} {a : ℝ} (h : is_local_min f a) : deriv f a = 0 :=
h.deriv_eq_zero

example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
  (hfc : continuous_on f (Icc a b)) (hfI : f a = f b) :
  ∃ c ∈ Ioo a b, deriv f c = 0 :=
exists_deriv_eq_zero f hab hfc hfI

example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : continuous_on f (Icc a b))
 (hf' : differentiable_on ℝ f (Ioo a b)) :
 ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
exists_deriv_eq_slope f hab hf hf'

example : deriv (λ x : ℝ, x^5) 6 = 5 * 6^4 := by simp

example (x₀ : ℝ) (h₀ : x₀ ≠ 0) : deriv (λ x : ℝ, 1 / x) x₀ = -(x₀^2)⁻¹ := by simp

example : deriv sin π = -1 := by simp

example (x₀ : ℝ) (h : x₀ ≠ 0) :
  deriv (λ x : ℝ, exp(x^2) / x^5) x₀ = (2 * x₀^2 - 5) * exp (x₀^2) / x₀^6 :=
begin
  have : x₀^5 ≠ 0, { exact pow_ne_zero 5 h, },
  field_simp,
  ring,
end

example (y : ℝ) : has_deriv_at (λ x : ℝ, 2 * x + 5) 2 y :=
begin
  have := ((has_deriv_at_id y).const_mul 2).add_const 5,
  rwa [mul_one] at this,
end

example (y : ℝ) : deriv (λ x : ℝ, 2 * x + 5) y = 2 := by simp

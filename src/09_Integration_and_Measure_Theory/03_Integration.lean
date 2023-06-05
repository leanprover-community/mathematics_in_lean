import analysis.normed_space.finite_dimension
import analysis.convolution
import measure_theory.function.jacobian
import measure_theory.integral.bochner
import measure_theory.measure.lebesgue

open set filter
open_locale topological_space filter ennreal
open measure_theory

noncomputable theory

variables {α : Type*} [measurable_space α]
variables {μ : measure α}

section

variables {E : Type*} [normed_group E] [normed_space ℝ E] [complete_space E]
  {f : α → E}

example {f g : α → E} (hf : integrable f μ) (hg : integrable g μ) :
  ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
integral_add hf hg

example {s : set α} (c : E) :
  ∫ x in s, c ∂μ = (μ s).to_real • c :=
set_integral_const c

example {F : ℕ → α → E} {f : α → E} (bound : α → ℝ)
  (hmeas : ∀ n, ae_strongly_measurable (F n) μ)
  (hint : integrable bound μ)
  (hbound : ∀ n, ∀ᵐ a ∂μ, ∥F n a∥ ≤ bound a)
  (hlim : ∀ᵐ a ∂μ, tendsto (λ (n : ℕ), F n a) at_top (𝓝 (f a))) :
  tendsto (λ n, ∫ a, F n a ∂μ) at_top (𝓝 (∫ a, f a ∂μ)) :=
tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim

example
  {α : Type*} [measurable_space α]
  {μ : measure α} [sigma_finite μ]
  {β : Type*} [measurable_space β] {ν : measure β} [sigma_finite ν]
  (f : α × β → E) (hf : integrable f (μ.prod ν)) :
  ∫ z, f z ∂μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
integral_prod f hf

end
section
open_locale convolution

variables {𝕜 : Type*} {G : Type*} {E : Type*} {E' : Type*} {F : Type*} [normed_group E]
  [normed_group E'] [normed_group F] [nondiscrete_normed_field 𝕜]
  [normed_space 𝕜 E] [normed_space 𝕜 E'] [normed_space 𝕜 F]
  [measurable_space G] [normed_space ℝ F] [complete_space F] [has_sub G]

example (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F) (μ : measure G) :
  f ⋆[L, μ] g = λ x, ∫ t, L (f t) (g (x - t)) ∂μ :=
rfl

end
example {E : Type*} [normed_group E] [normed_space ℝ E] [finite_dimensional ℝ E]
  [measurable_space E] [borel_space E] (μ : measure E) [μ.is_add_haar_measure]
  {F : Type*}[normed_group F] [normed_space ℝ F] [complete_space F]
  {s : set E} {f : E → E} {f' : E → (E →L[ℝ] E)}
  (hs : measurable_set s)
  (hf : ∀ (x : E), x ∈ s → has_fderiv_within_at f (f' x) s x)
  (h_inj : inj_on f s)
  (g : E → F) :
  ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ :=
integral_image_eq_integral_abs_det_fderiv_smul μ hs hf h_inj g

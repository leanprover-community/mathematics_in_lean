import analysis.normed_space.banach_steinhaus
import analysis.normed_space.finite_dimension

import analysis.calculus.inverse

open set filter
open_locale topological_space filter

noncomputable theory

section
variables {E : Type*} [normed_group E]

example (x : E) : 0 ≤ ∥x∥ :=
norm_nonneg x

example {x : E} : ∥x∥ = 0 ↔ x = 0 :=
norm_eq_zero

example (x y : E) : ∥x + y∥ ≤ ∥x∥ + ∥y∥ :=
norm_add_le x y

example : metric_space E := by apply_instance

example {X : Type*} [topological_space X] {f : X → E} (hf : continuous f) :
  continuous (λ x, ∥f x∥) :=
hf.norm

variables [normed_space ℝ E]

example (a : ℝ) (x : E) : ∥a • x∥ = |a| * ∥x∥ :=
norm_smul a x

example [finite_dimensional ℝ E] : complete_space E :=
by apply_instance

example (𝕜 : Type*) [nondiscrete_normed_field 𝕜] (x y : 𝕜) : ∥x * y∥ = ∥x∥ * ∥y∥ :=
norm_mul x y

example (𝕜 : Type*) [nondiscrete_normed_field 𝕜] : ∃ x : 𝕜, 1 < ∥x∥ :=
normed_field.exists_one_lt_norm 𝕜

example (𝕜 : Type*) [nondiscrete_normed_field 𝕜] (E : Type*) [normed_group E]
  [normed_space 𝕜 E] [complete_space 𝕜] [finite_dimensional 𝕜 E] : complete_space E :=
finite_dimensional.complete 𝕜 E

end

section
variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
          {E : Type*} [normed_group E] [normed_space 𝕜 E]
          {F : Type*} [normed_group F] [normed_space 𝕜 F]

example : E →L[𝕜] E := continuous_linear_map.id 𝕜 E

example (f : E →L[𝕜] F) : E → F :=
f

example (f : E →L[𝕜] F) : continuous f :=
f.cont

example (f : E →L[𝕜] F) (x y : E) : f (x + y) = f x + f y :=
f.map_add x y

example (f : E →L[𝕜] F) (a : 𝕜) (x : E) : f (a • x) = a • f x :=
f.map_smul a x

variables (f : E →L[𝕜] F)

example (x : E) : ∥f x∥ ≤ ∥f∥ * ∥x∥ :=
f.le_op_norm x

example {M : ℝ} (hMp: 0 ≤ M) (hM : ∀ x, ∥f x∥ ≤ M * ∥x∥) :
  ∥f∥ ≤ M :=
f.op_norm_le_bound hMp hM

end

section
variables
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]

open metric

example {ι : Type*} [complete_space E] {g : ι → E →L[𝕜] F}
  (h : ∀ x, ∃ C, ∀ i, ∥g i x∥ ≤ C) :
  ∃ C', ∀ i, ∥g i∥ ≤ C' :=
begin
  /- sequence of subsets consisting of those `x : E` with norms `∥g i x∥` bounded by `n` -/
  let e : ℕ → set E := λ n, ⋂ i : ι, { x : E | ∥g i x∥ ≤ n },
  /- each of these sets is closed -/
  have hc : ∀ n : ℕ, is_closed (e n),
  sorry,
  /- the union is the entire space; this is where we use `h` -/
  have hU : (⋃ n : ℕ, e n) = univ,
  sorry,
  /- apply the Baire category theorem to conclude that for some `m : ℕ`,
     `e m` contains some `x` -/
  obtain ⟨m, x, hx⟩ : ∃ m, ∃ x, x ∈ interior (e m) := sorry,
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x ε ⊆ interior (e m) := sorry,
  obtain ⟨k, hk⟩ : ∃ k : 𝕜, 1 < ∥k∥ := sorry,
  /- show all elements in the ball have norm bounded by `m` after applying any `g i` -/
  have real_norm_le : ∀ (z ∈ ball x ε) (i : ι), ∥g i z∥ ≤ m,
  sorry,
  have εk_pos : 0 < ε / ∥k∥ := sorry,
  refine ⟨(m + m : ℕ) / (ε / ∥k∥),
           λ i, continuous_linear_map.op_norm_le_of_shell ε_pos _ hk _⟩,
  sorry,
  sorry
end

end

open asymptotics
open_locale asymptotics

example {α : Type*} {E : Type*} [normed_group E] {F : Type*} [normed_group F]
  (c : ℝ) (l : filter α) (f : α → E) (g : α → F) :
  is_O_with c l f g ↔ ∀ᶠ x in l, ∥ f x ∥ ≤ c * ∥ g x ∥ :=
is_O_with_iff

example {α : Type*} {E : Type*} [normed_group E] {F : Type*} [normed_group F]
  (c : ℝ) (l : filter α) (f : α → E) (g : α → F) :
  f =O[l] g ↔ ∃ C, is_O_with C l f g :=
is_O_iff_is_O_with

example {α : Type*} {E : Type*} [normed_group E] {F : Type*} [normed_group F]
  (c : ℝ) (l : filter α) (f : α → E) (g : α → F) :
  f =o[l] g ↔ ∀ C > 0, is_O_with C l f g :=
is_o_iff_forall_is_O_with

example {α : Type*} {E : Type*} [normed_group E] (c : ℝ) (l : filter α) (f g : α → E) :
  f ~[l] g ↔ (f - g) =o[l] g :=
iff.rfl

section
variables
  {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
  {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
  has_fderiv_at f f' x₀ ↔ (λ x, f x - f x₀ - f' (x - x₀)) =o[𝓝 x₀] (λ x, x - x₀) :=
iff.rfl

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : has_fderiv_at f f' x₀) :
  fderiv 𝕜 f x₀ = f' :=
hff'.fderiv

example (n : ℕ) (f : E → F) : E → (E [×n]→L[𝕜] F) :=
iterated_fderiv 𝕜 n f

example (n : with_top ℕ) {f : E → F} :
  cont_diff 𝕜 n f ↔
    (∀ (m : ℕ), (m : with_top ℕ) ≤ n → continuous (λ x, iterated_fderiv 𝕜 m f x))
  ∧ (∀ (m : ℕ), (m : with_top ℕ) < n → differentiable 𝕜 (λ x, iterated_fderiv 𝕜 m f x)) :=
cont_diff_iff_continuous_differentiable

example {𝕂 : Type*} [is_R_or_C 𝕂] {E : Type*} [normed_group E] [normed_space 𝕂 E]
  {F : Type*} [normed_group F] [normed_space 𝕂 F]
  {f : E → F} {x : E} {n : with_top ℕ}
  (hf : cont_diff_at 𝕂 n f x) (hn : 1 ≤ n) :
  has_strict_fderiv_at f (fderiv 𝕂 f x) x :=
hf.has_strict_fderiv_at hn

section local_inverse
variables [complete_space E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

example (hf : has_strict_fderiv_at f ↑f' a) : F → E :=
has_strict_fderiv_at.local_inverse f f' a hf

example  (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  ∀ᶠ x in 𝓝 a, hf.local_inverse f f' a (f x) = x :=
hf.eventually_left_inverse

example  (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  ∀ᶠ x in 𝓝 (f a), f (hf.local_inverse f f' a x) = x :=
hf.eventually_right_inverse

example [complete_space E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
    (hf : has_strict_fderiv_at f ↑f' a) :
  has_strict_fderiv_at (has_strict_fderiv_at.local_inverse f f' a hf)
    (f'.symm : F →L[𝕜] E) (f a) :=
has_strict_fderiv_at.to_local_inverse hf

end local_inverse

#check has_fderiv_within_at
#check has_fderiv_at_filter

end
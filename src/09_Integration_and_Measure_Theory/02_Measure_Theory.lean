import analysis.normed_space.finite_dimension
import analysis.convolution
import measure_theory.function.jacobian
import measure_theory.integral.bochner
import measure_theory.measure.lebesgue

open set filter
open_locale topological_space filter ennreal
noncomputable theory

variables {α : Type*} [measurable_space α]

example : measurable_set (∅ : set α) := measurable_set.empty

example : measurable_set (univ : set α) := measurable_set.univ

example {s : set α} (hs : measurable_set s) : measurable_set sᶜ :=
hs.compl

example : encodable ℕ :=
by apply_instance

example (n : ℕ) : encodable (fin n) :=
by apply_instance

variables {ι : Type*} [encodable ι]

example {f : ι → set α} (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋃ b, f b) :=
measurable_set.Union h

example {f : ι → set α} (h : ∀ b, measurable_set (f b)) :
  measurable_set (⋂ b, f b) :=
measurable_set.Inter h

open measure_theory

variables {μ : measure α}

example (s : set α) : μ s = ⨅ t (st : s ⊆ t) (ht : measurable_set t), μ t :=
measure_eq_infi s

example  (s : ι → set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
measure_Union_le s

example {f : ℕ → set α}
    (hmeas : ∀ i, measurable_set (f i)) (hdis : pairwise (disjoint on f)) :
  μ (⋃ i, f i) = ∑' i, μ (f i) :=
μ.m_Union hmeas hdis

example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in μ.ae, P x :=
iff.rfl

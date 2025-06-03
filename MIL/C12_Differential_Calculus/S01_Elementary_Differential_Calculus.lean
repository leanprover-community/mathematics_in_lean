import MIL.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

open Set Filter
open Topology Filter Classical Real

noncomputable section

open Real

/-- The sin function has derivative 1 at 0. -/
example : HasDerivAt sin 1 0 := by simpa using hasDerivAt_sin 0

example (x : ℝ) : DifferentiableAt ℝ sin x :=
  (hasDerivAt_sin x).differentiableAt

example {f : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt f a x) : deriv f x = a :=
  h.deriv

example {f : ℝ → ℝ} {x : ℝ} (h : ¬DifferentiableAt ℝ f x) : deriv f x = 0 :=
  deriv_zero_of_not_differentiableAt h

example {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  deriv_add hf hg

example {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMin f a) : deriv f a = 0 :=
  h.deriv_eq_zero

open Set

example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hfc hfI

example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hf' : DifferentiableOn ℝ f (Ioo a b)) : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope f hab hf hf'

example : deriv (fun x : ℝ ↦ x ^ 5) 6 = 5 * 6 ^ 4 := by simp

example : deriv sin π = -1 := by simp

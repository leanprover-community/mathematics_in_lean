import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Filter

noncomputable section

variable {α : Type _} [MeasurableSpace α]

variable {ι : Type _} [Encodable ι]

open MeasureTheory
variable {μ : Measure α}


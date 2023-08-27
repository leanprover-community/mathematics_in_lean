import MIL.Common
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Filter

noncomputable section

variable {α : Type*} [MeasurableSpace α]

variable {ι : Type*} [Encodable ι]

open MeasureTheory
variable {μ : Measure α}


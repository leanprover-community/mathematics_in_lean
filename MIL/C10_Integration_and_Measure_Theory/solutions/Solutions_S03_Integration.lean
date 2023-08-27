import MIL.Common
import Mathlib.Analysis.NormedSpace.FiniteDimension
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set Filter

open Topology Filter ENNReal

open MeasureTheory

noncomputable section
variable {α : Type*} [MeasurableSpace α]
variable {μ : Measure α}


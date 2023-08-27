import MIL.Common
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.Convolution

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

open Set Filter

open Topology Filter

noncomputable section


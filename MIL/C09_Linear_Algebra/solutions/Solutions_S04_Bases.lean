import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

  have F : M = P' * M' * P := by
    rw [← toMatrix_comp, ← toMatrix_comp, id_comp, comp_id]
  have F' : P' * P = 1 := by
    rw [← toMatrix_comp, id_comp, toMatrix_id]
  rw [F, Matrix.det_mul, Matrix.det_mul,
      show P'.det * M'.det * P.det = P'.det * P.det * M'.det by ring, ← Matrix.det_mul, F',
      Matrix.det_one, one_mul]
end

  rw [← finrank_pos_iff (R := K)]
  have := Submodule.finrank_sup_add_finrank_inf_eq E F
  have := Submodule.finrank_le E
  have := Submodule.finrank_le F
  have := Submodule.finrank_le (E ⊔ F)
  linarith
end


import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import MIL.Common

def preimage (φ : V →ₗ[K] W) (H : Submodule K W) : Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
    dsimp
    rw [Set.mem_preimage, map_zero]
    exact H.zero_mem
  add_mem' := by
    rintro a b ha hb
    rw [Set.mem_preimage, map_add]
    apply H.add_mem <;> assumption
  smul_mem' := by
    dsimp
    rintro a v hv
    rw [Set.mem_preimage, map_smul]
    exact H.smul_mem a hv

  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h - ⟨x, hx, rfl⟩
    exact h hx


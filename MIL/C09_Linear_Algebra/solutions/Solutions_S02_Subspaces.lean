import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Charpoly.Basic

import MIL.Common

def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
    Submodule K V where
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

  · rintro x (hx|hx)
    · use x, hx, 0, T.zero_mem
      module
    · use 0, S.zero_mem, x, hx
      module
  · use 0, S.zero_mem, 0, T.zero_mem
    module
  · rintro - - ⟨s, hs, t, ht, rfl⟩ ⟨s', hs', t', ht', rfl⟩
    use s + s', S.add_mem hs hs', t + t', T.add_mem ht ht'
    module
  · rintro a - ⟨s, hs, t, ht, rfl⟩
    use a • s, S.smul_mem a hs, a • t, T.smul_mem a ht
    module

  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h - ⟨x, hx, rfl⟩
    exact h hx

  toFun F := ⟨comap E.mkQ F, by
    conv_lhs => rw [← E.ker_mkQ, ← comap_bot]
    gcongr
    apply bot_le⟩
  invFun P := map E.mkQ P
  left_inv P := by
    dsimp
    rw [Submodule.map_comap_eq, E.range_mkQ]
    exact top_inf_eq P
  right_inv := by
    intro P
    ext x
    dsimp only
    rw [Submodule.comap_map_eq, E.ker_mkQ, sup_of_le_left]
    exact P.2

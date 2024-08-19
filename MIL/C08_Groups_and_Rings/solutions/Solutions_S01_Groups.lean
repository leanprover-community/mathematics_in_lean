import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

import MIL.Common

def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    use 1
    constructor
    exact H.one_mem
    group
  inv_mem' := by
    dsimp
    rintro - ⟨h, h_in, rfl⟩
    use h⁻¹, H.inv_mem h_in
    group
  mul_mem' := by
    dsimp
    rintro - - ⟨h, h_in, rfl⟩ ⟨k, k_in, rfl⟩
    use h*k, H.mul_mem h_in k_in
    group

section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
  intro x hx
  rw [mem_comap] at * -- Lean does not need this line
  exact hST hx

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  intro x hx
  rw [mem_map] at * -- Lean does not need this line
  rcases hx with ⟨y, hy, rfl⟩
  use y, hST hy

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
    comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  -- The whole proof could be ``rfl``, but let's decompose it a bit.
  ext x
  simp only [mem_comap]
  rfl

-- Pushing a subgroup along one homomorphism and then another is equal to
-- pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
    map (ψ.comp φ) S = map ψ (S.map φ) := by
  ext x
  simp only [mem_map]
  constructor
  · rintro ⟨y, y_in, hy⟩
    exact ⟨φ y, ⟨y, y_in, rfl⟩, hy⟩
  · rintro ⟨y, ⟨z, z_in, hz⟩, hy⟩
    use z, z_in
    calc ψ.comp φ z = ψ (φ z) := rfl
    _               = ψ y := by congr
    _               = x := hy

end exercises

open scoped Classical

open Subgroup

lemma eq_bot_iff_card {G : Type*} [Group G] {H : Subgroup G} :
    H = ⊥ ↔ Nat.card H = 1 := by
  suffices (∀ x ∈ H, x = 1) ↔ ∃ x ∈ H, ∀ a ∈ H, a = x by
    simpa [eq_bot_iff_forall, Nat.card_eq_one_iff_exists]
  constructor
  · intro h
    use 1, H.one_mem
  · rintro ⟨y, -, hy'⟩ x hx
    calc x = y := hy' x hx
    _      = 1 := (hy' 1 H.one_mem).symm

lemma inf_bot_of_coprime {G : Type*} [Group G] (H K : Subgroup G)
    (h : (Nat.card H).Coprime (Nat.card K)) : H ⊓ K = ⊥ := by
  have D₁ : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card H := card_dvd_of_le inf_le_left
  have D₂ : Nat.card (H ⊓ K : Subgroup G) ∣ Nat.card K := card_dvd_of_le inf_le_right
  exact eq_bot_iff_card.2 (Nat.eq_one_of_dvd_coprimes h D₁ D₂)

noncomputable section GroupActions

variable {G : Type*} [Group G]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
  ext x
  simp [conjugate]

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
    exact conjugate_one
  mul_smul := by
    intro x y H
    ext z
    constructor
    · rintro ⟨h, h_in, rfl⟩
      use y*h*y⁻¹
      constructor
      · use h
      · group
    · rintro ⟨-, ⟨h, h_in, rfl⟩, rfl⟩
      use h, h_in
      group

end GroupActions

noncomputable section QuotientGroup

section
variable {G : Type*} [Group G] {H K : Subgroup G}

open MonoidHom

#check Nat.card_pos -- The nonempty argument will be automatically inferred for subgroups
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
    Nat.card (G ⧸ H) = Nat.card K := by
  have := calc
    Nat.card (G ⧸ H) * Nat.card H = Nat.card G := by rw [← H.index_eq_card, H.index_mul_card]
    _                             = Nat.card K * Nat.card H := by rw [h', mul_comm]

  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos this

variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K)
  (h' : Nat.card G = Nat.card H * Nat.card K)

#check Nat.bijective_iff_injective_and_card
#check ker_eq_bot_iff
#check restrict
#check ker_restrict

def iso₁ [Fintype G] (h : Disjoint H K) (h' : Nat.card G = Nat.card H * Nat.card K) : K ≃* G ⧸ H := by
  apply MulEquiv.ofBijective ((QuotientGroup.mk' H).restrict K)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, (QuotientGroup.mk' H).ker_restrict K]
    simp [h]
  · symm
    exact aux_card_eq h'

def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
  apply MulEquiv.ofBijective <| (QuotientGroup.mk' K).prod (QuotientGroup.mk' H)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · rw [← ker_eq_bot_iff, ker_prod]
    simp [h.symm.eq_bot]
  · rw [Nat.card_prod]
    rw [aux_card_eq h', aux_card_eq (mul_comm (Nat.card H) _▸ h'), h']

def finalIso : G ≃* H × K :=
  (iso₂ h h').trans ((iso₁ h.symm (mul_comm (Nat.card H) _ ▸ h')).prodCongr (iso₁ h h')).symm

end
end QuotientGroup

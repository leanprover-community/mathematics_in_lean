import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    · apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · trans x ⊓ y
      apply inf_le_left
      apply inf_le_left
    apply le_inf
    · trans x ⊓ y
      apply inf_le_left
      apply inf_le_right
    apply inf_le_right
  apply le_inf
  · apply le_inf
    · apply inf_le_left
    trans y ⊓ z
    apply inf_le_right
    apply inf_le_left
  trans y ⊓ z
  apply inf_le_right
  apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    · apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      apply le_sup_left
      · trans y ⊔ z
        apply le_sup_left
        apply le_sup_right
    trans y ⊔ z
    apply le_sup_right
    apply le_sup_right
  apply sup_le
  · trans x ⊔ y
    apply le_sup_left
    apply le_sup_left
  apply sup_le
  · trans x ⊔ y
    apply le_sup_right
    apply le_sup_left
  apply le_sup_right

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  apply le_inf
  · apply le_refl
  apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    apply inf_le_left
  apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h, ← sup_assoc, @inf_comm _ _ c a,
    absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, @sup_comm _ _ (a ⊓ b), absorb2, @sup_comm _ _ (a ⊓ b), h, ← inf_assoc, @sup_comm _ _ c a,
    absorb1, sup_comm]

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b]
  apply add_le_add_left h

theorem aux2 (h : 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a, ← sub_add_cancel b a, add_comm (b - a)]
  apply add_le_add_left h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) * c := mul_nonneg (aux1 _ _ h) h'
  rw [sub_mul] at h1
  exact aux2 _ _ h1

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

example (x y : X) : 0 ≤ dist x y :=by
  have : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  linarith [dist_comm x y]

end


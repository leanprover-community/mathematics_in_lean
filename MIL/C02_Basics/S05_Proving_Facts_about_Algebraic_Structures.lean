import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)

#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  -- suggest_tactics
  -- aesop?
  rename_i inst
  rw [inf_comm]

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  -- suggest_tactics
  -- aesop?
  rename_i inst
  rw [inf_assoc]

example : x ⊔ y = y ⊔ x := by
  -- suggest_tactics
  -- aesop?
  rename_i inst
  rw [sup_comm]

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  -- suggest_tactics
  -- aesop?
  rename_i inst
  rw [sup_assoc]

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  -- suggest_tactics
  -- aesop?
  rename_i inst
  simp_all only [ge_iff_le, le_sup_left, inf_of_le_left]

theorem absorb2 : x ⊔ x ⊓ y = x := by
  -- suggest_tactics
  -- aesop?
  rename_i inst
  simp_all only [ge_iff_le, inf_le_left, sup_of_le_left]

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  -- suggest_tactics
  -- aesop?
  rename_i inst
  simp_all only [sub_nonneg]

example (h: 0 ≤ b - a) : a ≤ b := by
  -- suggest_tactics
  -- aesop?
  rename_i inst
  simp_all only [sub_nonneg]

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  -- suggest_tactics
  -- aesop?
  rename_i inst
  exact mul_le_mul_of_nonneg_right h h'

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  -- suggest_tactics
  -- aesop?
  rename_i inst x_1 y_1
  exact dist_nonneg

end

import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  -- suggest_tactics
  -- aesop?
  simp_all only [image_subset_iff]

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  -- suggest_tactics
  -- aesop?
  simp_all only [preimage_image_eq]
  rfl

example : f '' (f ⁻¹' u) ⊆ u := by
  -- suggest_tactics
  -- aesop?
  simp_all only [image_subset_iff]
  rfl

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  -- suggest_tactics
  -- aesop?
  simp_all only [image_preimage_eq]
  rfl

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  -- suggest_tactics
  -- aesop?
  simp_all only [image_subset_iff]
  intro u hu
  simp_all only [mem_preimage, mem_image]
  exact ⟨u, h hu, rfl⟩

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  -- suggest_tactics
  -- aesop?
  apply preimage_mono h

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  -- suggest_tactics
  -- aesop?
  simp_all only [preimage_union]

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  -- suggest_tactics
  -- aesop?
  simp_all only [subset_inter_iff, image_subset_iff]
  apply And.intro
  · intro y hy
    simp_all only [mem_inter_iff, mem_preimage, mem_image]
    unhygienic with_reducible aesop_destruct_products
    exact ⟨y, left, rfl⟩
  · intro x hx
    simp_all only [mem_inter_iff, mem_preimage, mem_image]
    unhygienic with_reducible aesop_destruct_products
    exact ⟨x, right, rfl⟩

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  -- aesop?
  simp_all only [preimage_diff]
  rfl
  -- suggest_tactics

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  -- aesop?
  rw [image_inter_preimage]
  -- suggest_tactics

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  -- aesop?
  simp_all only [subset_inter_iff, image_subset_iff, inter_subset_right, and_true]
  intro x hx
  simp_all only [mem_inter_iff, mem_preimage, mem_image]
  unhygienic with_reducible aesop_destruct_products
  exact ⟨x, left, rfl⟩
  -- suggest_tactics

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  -- aesop?
  simp_all only [preimage_inter, subset_inter_iff, inter_subset_right, and_true]
  intro x hx
  simp_all only [mem_inter_iff, mem_preimage, mem_image]
  unhygienic with_reducible aesop_destruct_products
  exact ⟨x, left, rfl⟩

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  -- aesop?
  simp_all only [preimage_union, union_subset_iff, subset_union_right, and_true]
  intro x hx
  simp_all only [mem_union, mem_preimage, mem_image]
  exact Or.inl ⟨x, hx, rfl⟩

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp
  constructor
  · rintro ⟨x, ⟨i, xAi⟩, fxeq⟩
    use i, x
  rintro ⟨i, x, xAi, fxeq⟩
  exact ⟨x, ⟨i, xAi⟩, fxeq⟩

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  intro y; simp
  intro x h fxeq i
  use x
  exact ⟨h i, fxeq⟩

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  intro y; simp
  intro h
  rcases h i with ⟨x, xAi, fxeq⟩
  use x; constructor
  · intro i'
    rcases h i' with ⟨x', x'Ai, fx'eq⟩
    have : f x = f x' := by rw [fxeq, fx'eq]
    have : x = x' := injf this
    rw [this]
    exact x'Ai
  exact fxeq

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  ext x
  simp

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  ext x
  simp

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  -- aesop?
  simp_all only [ge_iff_le]
  intro x hx y hy hxy
  simp_all only [mem_setOf_eq, sqrt_inj]

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  -- aesop?
  simp_all only [ge_iff_le]
  rintro a ha b hb hab
  simp_all only [mem_setOf_eq, ge_iff_le, zero_lt_two, pow_left_inj]

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f :=
  sorry

example : Surjective f ↔ RightInverse (inverse f) f :=
  sorry

end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂ : j ∈ S := by
    -- suggest_tactics
    sorry
  have h₃ : j ∉ S := by
    sorry
  contradiction

-- COMMENTS: TODO: improve this
end

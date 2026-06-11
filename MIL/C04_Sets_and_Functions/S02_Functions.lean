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

-- the image of a set under a function
example : f '' s = image f s := rfl
example : {y | ∃ x, x ∈ s ∧ f x =y} = image f s := rfl

-- preimage of a set
example : f⁻¹' u = preimage f u := rfl
example : {x | f x ∈ u} = preimage f u := rfl

-- singleton sets don't work
example (y:u): f⁻¹' y = preimage f { z: β | z=y} := rfl
variable (y':u)
#check { z: β | z=y'} -- this is the singleton set {y}
#check (· =y') -- this is predicate for equal to y
example (y:u): (· =y) = { z: u | z=y} := rfl

-- note that u → Prop does not have type Set β
example (y:u): f⁻¹' (· =y) = preimage f { z: u | z=y} := rfl

example (y:u): { z: β | z=y} = (· =y) := rfl


example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  -- rfl immediately substitutes equalities
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt
--use tactic applies rfl to close goals when it can
example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

#check subset_def
/--image f and preimage f are a Galois connection
between Set α and Set β-/
theorem gal_conn : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  case mpr =>
    rintro h y yfs
    rcases yfs with ⟨ x, xs, rfl ⟩
    rw [subset_def] at h
    apply h
    exact xs
  case mp =>
    rintro h x xs
    show (f x) ∈ v
    apply h
    exact ⟨ x, xs, rfl⟩ /-want to show f x satisfies
    ∃ x, x ∈ s ∧ f x =y
    see following example -/

example (x:α) (xs: x ∈ s) : f x ∈ f '' s := ⟨ x, xs, rfl ⟩
-- unfolding y ∈ f '' s
example (y: β) : (y ∈ f '' s) = (∃ x, x ∈ s ∧ f x = y) := rfl



example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x h
  --have h' : f x ∈ (f '' s) := h
  rcases h with ⟨w, ws, feq⟩ -- or rcases h' ...
  have hwx: w = x := h feq
  --rewrite [← hwx]; exact ws
  exact hwx ▸ ws

example : f '' (f ⁻¹' u) ⊆ u := by
  /- if you type, rintro ⟨
  vscode with fill put inaccessibles in the info view-/
  rintro _ ⟨w, fw_in_u, rfl ⟩
  exact fw_in_u

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro y yu
  rcases h y with ⟨_, rfl ⟩-- _ in preimage of y
  exact ⟨ _, yu, rfl ⟩

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) :=
fun y yu =>
  match h y with
  | ⟨x, h⟩ =>
  -- unlike rcases, match does not have the rfl tage
      ⟨x, yu, h⟩
      -- not sure why this errors


example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  constructor
  case mp =>
    rintro ⟨x, ⟨Ai, ⟨ i, rfl ⟩, hx: x ∈ A i ⟩, rfl ⟩
    /-alternatively
    rintro ⟨ x,hai, rfl ⟩
    rcases hai with ⟨Ai, ⟨ i, rfl ⟩, hx: x ∈ A i ⟩-/
    simp
    exact ⟨ i, x, hx, rfl ⟩
  case mpr =>
    rintro ⟨Ai, hai, yAi ⟩
    rcases hai with ⟨i, rfl⟩
    rcases yAi with ⟨ x, xAi, rfl⟩
    show_term
    simp --this simp is needed
    /-exact ⟨x, ⟨A i, {
      left := by simp
      right := xAi
    } ⟩, rfl ⟩-/
    exact ⟨x, ⟨i, xAi ⟩, rfl ⟩


example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  sorry

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos e
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
  intro x xpos y ypos e
  calc
    x = (sqrt x)^2 := by rw [sq_sqrt xpos]
    _ = (sqrt y)^2 := by rw [e]
    _ = y          := by rw [sq_sqrt ypos]


example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext x
  have mp: x ∈ sqrt '' {x | x ≥ 0} -> x ∈ {y | y ≥ 0} := by
    rintro ⟨w, wpos ,rfl⟩
    show sqrt w ≥ 0
    exact sqrt_nonneg w
  constructor
  · exact mp
  · rintro xpos: x ≥ 0
    let w := x^2
    have wpos : w ≥ 0 := by exact sq_nonneg x
    exact ⟨ w, wpos, sqrt_sq xpos⟩


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
#print LeftInverse
example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  case mp =>
    rintro inj a
    have h: f ((inverse f) (f a)) = f a := by
      apply inverse_spec
      exact ⟨ a, rfl ⟩
    exact inj h
  case mpr =>
   rintro invl a a' fxfy
   calc
     a = (inverse f) (f a) := by rw [invl a]
     _ = (inverse f) (f a') := by rw [fxfy]
     _ = a'                 := invl a'


example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  case mp =>
    rintro surj b
    apply inverse_spec
    exact surj b
  case mpr =>
    rintro invr b
    use (inverse f) b
    exact invr b




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
  have h₂ : j ∈ S
  sorry
  have h₃ : j ∉ S
  sorry
  contradiction

-- COMMENTS: TODO: improve this
end

import MIL.Common
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit true


def isMonoidHom₁ [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'
structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'
example : Continuous (id : ℝ → ℝ) := continuous_id
@[ext]
structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'

instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

attribute [coe] MonoidHom₁.toFun


example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 :=  f.map_one

@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun

@[ext]
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S



class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'


def badInst [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun


class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun


instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul


lemma map_inv_of_inv [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass₂.map_mul, h, MonoidHomClass₂.map_one]

example [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map_inv_of_inv f h

example [Ring R] [Ring S] (f : RingHom₁ R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map_inv_of_inv f h



class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    DFunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' _ _ := MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul


@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
MonoidHom₁ M N, OrderPresHom M N

class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β]

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    MonoidHomClass₃ (OrderPresMonoidHom α β) α β
  := sorry

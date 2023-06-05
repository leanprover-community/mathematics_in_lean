import data.real.basic

structure add_group₁ (α : Type*) :=
(add: α → α → α)
(zero: α)
(neg: α → α)
(add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z))
(add_zero: ∀ x : α, add x zero = x)
(zero_add: ∀ x : α, add x zero = x)
(add_left_neg : ∀ x : α, add (neg x) x = zero)

@[ext] structure point := (x : ℝ) (y : ℝ) (z : ℝ)

namespace point

def add (a b : point) : point := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

def neg (a : point) : point := ⟨-a.x, -a.y, -a.z⟩

def zero : point := ⟨0, 0, 0⟩

def add_group_point : add_group₁ point :=
{ add          := point.add,
  zero         := point.zero,
  neg          := point.neg,
  add_assoc    := by { simp [point.add, add_assoc] },
  add_zero     := by { simp [point.add, point.zero], intro, ext; refl },
  zero_add     := by { simp [point.add, point.zero], intro, ext; refl },
  add_left_neg := by { simp [point.add, point.neg, point.zero] } }

end point

class add_group₂ (α : Type*) :=
(add: α → α → α)
(zero: α)
(neg: α → α)
(add_assoc : ∀ x y z : α, add (add x y) z = add x (add y z))
(add_zero: ∀ x : α, add x zero = x)
(zero_add: ∀ x : α, add x zero = x)
(add_left_neg : ∀ x : α, add (neg x) x = zero)

instance has_add_add_group₂ {α : Type*} [add_group₂ α] :
has_add α := ⟨add_group₂.add⟩

instance has_zero_add_group₂ {α : Type*} [add_group₂ α] :
has_zero α := ⟨add_group₂.zero⟩

instance has_neg_add_group₂ {α : Type*} [add_group₂ α] :
has_neg α := ⟨add_group₂.neg⟩

instance : add_group₂ point :=
{ add          := point.add,
  zero         := point.zero,
  neg          := point.neg,
  add_assoc    := by { simp [point.add, add_assoc] },
  add_zero     := by { simp [point.add, point.zero], intro, ext; refl },
  zero_add     := by { simp [point.add, point.zero], intro, ext; refl },
  add_left_neg := by { simp [point.add, point.neg, point.zero] } }

section
variables (x y : point)

#check x + -y + 0
end


import topology.metric_space.basic

section
variables {α : Type*} [lattice α]
variables x y z : α

example : x ⊓ y = y ⊓ x :=
begin
  apply le_antisymm,
  repeat {
    apply le_inf,
    { apply inf_le_right },
    apply inf_le_left }
end

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) :=
begin
  apply le_antisymm,
  { apply le_inf,
    { apply le_trans,
      apply inf_le_left,
      apply inf_le_left },
    apply le_inf,
    { apply le_trans,
      apply inf_le_left,
      apply inf_le_right },
    apply inf_le_right  },
  apply le_inf,
  { apply le_inf,
    { apply inf_le_left },
    apply le_trans,
    apply inf_le_right,
    apply inf_le_left },
  apply le_trans,
  apply inf_le_right,
  apply inf_le_right
end

example : x ⊔ y = y ⊔ x :=
begin
  apply le_antisymm,
  repeat {
    apply sup_le,
    { apply le_sup_right },
    apply le_sup_left }
end

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) :=
begin
  apply le_antisymm,
  { apply sup_le,
    { apply sup_le,
      apply le_sup_left,
      { apply le_trans,
        apply @le_sup_left _ _ y z,
        apply le_sup_right } },
    apply le_trans,
    apply @le_sup_right _ _ y z,
    apply le_sup_right },
  apply sup_le,
  { apply le_trans,
    apply @le_sup_left _ _ x y,
    apply le_sup_left },
  apply sup_le,
  { apply le_trans,
    apply @le_sup_right _ _ x y,
    apply le_sup_left },
  apply le_sup_right
end

theorem absorb1 : x ⊓ (x ⊔ y) = x :=
begin
  apply le_antisymm,
  { apply inf_le_left },
  apply le_inf,
  { apply le_refl },
  apply le_sup_left
end

theorem absorb2 : x ⊔ (x ⊓ y) = x :=
begin
  apply le_antisymm,
  { apply sup_le,
    { apply le_refl },
    apply inf_le_left },
  apply le_sup_left
end

end

section
variables {α : Type*} [distrib_lattice α]
variables x y z : α

#check (inf_sup_left : x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z))
#check (inf_sup_right : (x ⊔ y) ⊓ z = (x ⊓ z) ⊔ (y ⊓ z))
#check (sup_inf_left : x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : (x ⊓ y) ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))

end

section
variables {α : Type*} [lattice α]
variables a b c : α

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)) :
  a ⊔ (b ⊓ c) = (a ⊔ b) ⊓ (a ⊔ c) :=
by rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h,
    ←sup_assoc, @inf_comm _ _ c a, absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)) :
  a ⊓ (b ⊔ c) = (a ⊓ b) ⊔ (a ⊓ c) :=
by rw [h, @sup_comm _ _ (a ⊓ b), absorb2, @sup_comm _ _ (a ⊓ b), h,
    ←inf_assoc, @sup_comm _ _ c a, absorb1, sup_comm]

end

section
variables {R : Type*} [ordered_ring R]
variables a b c : R

theorem aux1 : a ≤ b → 0 ≤ b - a :=
begin
  intro h,
  rw [←sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b],
  apply add_le_add_left h
end

theorem aux2 : 0 ≤ b - a → a ≤ b :=
begin
  intro h,
  rw [←add_zero a, ←sub_add_cancel b a, add_comm (b - a)],
  apply add_le_add_left h
end

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c :=
begin
  have h1 : 0 ≤ (b - a) * c,
  { exact mul_nonneg (aux1 _ _ h) h' },
  rw sub_mul at h1,
  exact aux2 _ _ h1
end

end

section
variables {X : Type*} [metric_space X]
variables x y z : X

example (x y : X) : 0 ≤ dist x y :=
begin
  have : 0 ≤ dist x y + dist y x,
  { rw [←dist_self x],
    apply dist_triangle },
  linarith [dist_comm x y]
end

end


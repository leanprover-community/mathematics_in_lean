import order.lattice

variables {α : Type*} [lattice α]
variables x y z : α

-- BEGIN
example : x ⊓ (x ⊔ y) = x := sorry
example : x ⊔ (x ⊔ y) = x := sorry
-- END
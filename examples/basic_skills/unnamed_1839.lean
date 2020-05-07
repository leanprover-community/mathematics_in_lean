variables {R : Type*} [ordered_ring R]
variables a b c : R

-- BEGIN
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
-- END
import data.set.lattice
import data.nat.prime

open set nat

def primes : set ℕ := {x | prime x}

-- BEGIN
example : (⋃ p ∈ primes, {x | x ≤ p}) = univ :=
sorry
-- END
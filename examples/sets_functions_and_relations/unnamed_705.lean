import data.set.lattice
import data.nat.prime

open set nat

-- BEGIN
def primes : set ℕ := {x | prime x}

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, rw mem_bUnion_iff, refl }

example : (⋃ p ∈ primes, {x | p^2 ∣ x}) = {x | ∃ p ∈ primes, p^2 ∣ x} :=
by { ext, simp }

example : (⋂ p ∈ primes, {x | ¬ p ∣ x}) ⊆ {x | x < 2} :=
begin
  intro x,
  contrapose!,
  simp,
  apply exists_prime_and_dvd
end
-- END
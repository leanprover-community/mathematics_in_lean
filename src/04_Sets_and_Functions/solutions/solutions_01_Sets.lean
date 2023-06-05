import data.set.lattice
import data.nat.parity
import tactic

section
variable {α : Type*}
variables (s t u : set α)

open set

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u):=
begin
  rintros x (⟨xs, xt⟩ | ⟨xs, xu⟩),
  { use xs, left, exact xt },
  use xs, right, exact xu
end

example : s \ (t ∪ u) ⊆ s \ t \ u :=
begin
  rintros x ⟨xs, xntu⟩,
  use xs,
  { intro xt, exact xntu (or.inl xt) },
  intro xu,
  apply xntu (or.inr xu)
end

example : s ∩ t = t ∩ s :=
subset.antisymm (λ x ⟨xs, xt⟩, ⟨xt, xs⟩) (λ x ⟨xt, xs⟩, ⟨xs, xt⟩)

example : s ∩ (s ∪ t) = s :=
begin
  ext x, split,
  { rintros ⟨xs, _⟩, exact xs },
  intro xs,
  use xs, left, exact xs
end

example : s ∪ (s ∩ t) = s :=
begin
  ext x, split,
  { rintros (xs | ⟨xs, xt⟩); exact xs },
  intro xs, left, exact xs
end

example : (s \ t) ∪ t = s ∪ t :=
begin
  ext x, split,
  { rintros (⟨xs, nxt⟩ | xt),
    { left, exact xs},
    right, exact xt },
  by_cases h : x ∈ t,
  { intro _, right, exact h },
  rintros (xs | xt),
  { left, use [xs, h] },
  right, use xt
end

example : (s \ t) ∪ (t \ s) = (s ∪ t) \ (s ∩ t) :=
begin
  ext x, split,
  { rintros (⟨xs, xnt⟩ | ⟨xt, xns⟩),
    { split, left, exact xs,
      rintros ⟨_, xt⟩, contradiction },
    split , right, exact xt,
    rintros ⟨xs, _⟩, contradiction },
  rintros ⟨xs | xt, nxst⟩,
  { left, use xs, intro xt,
    apply nxst,
    split; assumption },
  right, use xt, intro xs,
  apply nxst,
  split; assumption
end

example : { n | nat.prime n } ∩ { n | n > 2} ⊆ { n | ¬ even n } :=
begin
  intro n,
  simp,
  intro nprime,
  cases nat.prime.eq_two_or_odd nprime with h h,
  { rw h, intro, linarith },
  rw [nat.even_iff, h],
  norm_num
end

end
section
variables (s t : set ℕ)

section
variable (ssubt : s ⊆ t)

include ssubt

example (h₀ : ∀ x ∈ t, ¬ even x) (h₁ : ∀ x ∈ t, prime x) :
  ∀ x ∈ s, ¬ even x ∧ prime x :=
begin
  intros x xs,
  split,
  { apply h₀ x (ssubt xs) },
  apply h₁ x (ssubt xs)
end

example (h : ∃ x ∈ s, ¬ even x ∧ prime x) :
  ∃ x ∈ t, prime x :=
begin
  rcases h with ⟨x, xs, _, px⟩,
  use [x, ssubt xs, px]
end

end

end

section
variables {α I : Type*}
variables A B : I → set α
variable  s : set α
open set

example : s ∪ (⋂ i, A i) = ⋂ i, (A i ∪ s) :=
begin
  ext x,
  simp only [mem_union, mem_Inter],
  split,
  { rintros (xs | xI),
    { intro i, right, exact xs },
    intro i, left, exact xI i },
  intro h,
  by_cases xs : x ∈ s,
  { left, exact xs },
  right,
  intro i,
  cases h i,
  { assumption },
  contradiction
end

def primes : set ℕ := {x | nat.prime x}

example : (⋃ p ∈ primes, {x | x ≤ p}) = univ :=
begin
  apply eq_univ_of_forall,
  intro x,
  simp,
  rcases nat.exists_infinite_primes x with ⟨p, primep, pge⟩,
  use [p, pge, primep]
end

end


import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

section
variable {α : Type*}
variable (s t u : Set α)
open Set
/-set builder notation is a lambda expression in disguise!
-/
#check { x | s x }
#check λ x => s x
example : { x | s x } = (λ x => s x) := rfl
example : (s · ) = (λ x => s x) := rfl

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff--inter_def
  ] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun _x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  · right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  · right; exact ⟨xs, xu⟩
/-
* `{x | p x}` is elaborated as `Set.setOf fun x ↦ p x`
* `{x : α | p x}` is elaborated as `Set.setOf fun x : α ↦ p x`
* `{binder x | p x}`, where `x` is bound by the `binder` binder, is elaborated as
  `{x | binder x ∧ p x}`. The typical example is `{x ∈ s | p x}`, which is elaborated as
  `{x | x ∈ s ∧ p x}`. The possible binders are
  -/
#check s ∩ t
#check setOf
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x hstsu
  rcases hstsu with xst | xsu
  · exact ⟨ xst.1, .inl xst.2 ⟩ -- notation for union is same as ∨
  · exact ⟨ xsu.1, .inr xsu.2 ⟩
--read x∈ s ∩ t as (x ∈ s) ∧ (x ∈ t)

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  · show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
  rintro x ⟨xs, xntu⟩
  constructor
  · constructor
    · exact xs
    · exact xntu ∘ .inl
  · exact xntu ∘ .inr

#check Set α -- is defined as α → Prop
-- to show two functions are equal, use ext
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Set.ext fun _x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

example : s ∩ t = t ∩ s :=
  Subset.antisymm
    (λ x ⟨xs, xt⟩ => ⟨xt, xs⟩)
    (λ x ⟨xt, xs⟩ => ⟨xs, xt⟩)

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  case mp => intro ⟨xs, _⟩; exact xs
  case mpr =>
    intro xs
    exact ⟨xs, .inl xs⟩


example : s ∪ s ∩ t = s := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  case mp =>
    rintro (⟨xs, xnt⟩ | xt)
    case inl => exact .inl xs
    case inr => exact .inr xt
  case mpr =>
    rintro ( xs | xt )
    -- I think you need em for this one
    · rcases (Classical.em (x ∈ t)) with xt | xnt
      · right; assumption
      · exact .inl ⟨xs, xnt ⟩
    · exact .inr xt


example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry

def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp [-Nat.not_even_iff_odd]
  apply Classical.em

example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial

theorem prime_gt_2_not_even : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  rintro n ⟨ hp, hn2⟩ he--⟨e, he⟩
  simp only [mem_setOf] at * -- unfold n ∈ { n | P n}
  have he' :n %2 =0 := by exact Nat.even_iff.mp he
  have : n ≠ 2 := Nat.ne_of_gt hn2
  --have : (Dvd.dvd 2 n) := ⟨ e, he'⟩
  rcases Nat.Prime.eq_two_or_odd hp with h2 | hodd
  · contradiction
  · rw [he'] at hodd; contradiction
  --rw [Nat.odd_iff]


#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]

end

section

variable (s t : Set ℕ)

example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs

section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  rintro x xs
  constructor
  · apply h₀
    exact ssubt xs
  · apply h₁
    exact ssubt xs

-- not sure what the issue is here
example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x :=
  λ x xs =>
    ⟨ h₀ (ssubt xs), h₁ (ssubt xs)⟩

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨ x, xs, hne, hp⟩
  use x
  exact ⟨ ssubt xs , hp ⟩

end

end

section
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩
/-
theorem mem_iUnion {x : α} {s : ι → Set α} : (x ∈ ⋃ i, s i) ↔ ∃ i, x ∈ s i
-/
#check ⋃ (i:I), A i -- is a function α → Prop
/-(x ∈ ⋃ i, s i)
-- this is evaluation at x:α
-/

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i


example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  case mp =>
    rintro (xs | xa) i
    · right; assumption
    · left
      apply xa
      exact mem_range_self i

  case mpr =>
    rintro h
    by_cases xs : x ∈ s
    · left; assumption
    · right
      simp only [ mem_iInter]
      intro i
      --have hu: x ∈ A i ∪ s := h i
      rcases (h i) with (ha | hs)
      · assumption
      · contradiction


def primes : Set ℕ :=
  { x | Nat.Prime x }

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd

example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  simp only [mem_iUnion₂]
  let ⟨ p, ⟨hxp, hpp⟩⟩ := Nat.exists_infinite_primes x
  exact ⟨ p, hpp, hxp ⟩ -- pretty damn cool

end

section

open Set

variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl

end

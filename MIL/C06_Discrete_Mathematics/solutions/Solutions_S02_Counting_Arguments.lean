import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

open Finset

def triangle (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range (n+1) ×ˢ range (n+1) | p.1 < p.2}

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  apply Nat.eq_div_of_mul_eq_right (by norm_num)
  let turn (p : ℕ × ℕ) : ℕ × ℕ := (n - 1 - p.1, n - p.2)
  calc 2 * #(triangle n)
      = #(triangle n) + #(triangle n) := by
          ring
    _ = #(triangle n) + #(triangle n |>.image turn) := by
          rw [Finset.card_image_of_injOn]
          rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq; simp [turn]
          simp_all [triangle]; omega
    _ = #(range n ×ˢ range (n + 1)) := by
          rw [←Finset.card_union_of_disjoint]; swap
          . rw [Finset.disjoint_iff_ne]
            rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq; simp [turn] at *
            simp_all [triangle]; omega
          congr; ext p; rcases p with ⟨p1, p2⟩
          simp [triangle, turn]
          constructor
          . rintro (h | h) <;> omega
          rcases Nat.lt_or_ge p1 p2 with h | h
          . omega
          . intro h'
            right
            use n - 1 - p1, n - p2
            omega
    _ = (n + 1) * n := by
          simp [mul_comm]

def triangle' (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range n ×ˢ range n | p.1 ≤ p.2}

example (n : ℕ) : #(triangle' n) = #(triangle n) := by
  let f (p : ℕ × ℕ) : ℕ × ℕ := (p.1, p.2 + 1)
  have : triangle n = (triangle' n |>.image f) := by
    ext p; rcases p with ⟨p1, p2⟩
    simp [triangle, triangle', f]
    constructor
    . intro h
      use p1, p2 - 1
      omega
    . simp; omega
  rw [this, card_image_of_injOn]
  rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq; simp [f] at *

example {n : ℕ} (A : Finset ℕ)
    (hA : #(A) = n + 1)
    (hA' : A ⊆ range (2 * n)) :
    ∃ m ∈ A, ∃ k ∈ A, Nat.Coprime m k := by
  have : ∃ t ∈ range n, 1 < #({u ∈ A | u / 2 = t}) := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · intro u hu
      specialize hA' hu
      simp only [mem_range] at *
      exact Nat.div_lt_of_lt_mul hA'
    · simp [hA]
  rcases this with ⟨t, ht, ht'⟩
  simp only [one_lt_card, mem_filter] at ht'
  rcases ht' with ⟨m, ⟨hm, hm'⟩, k, ⟨hk, hk'⟩, hmk⟩
  have : m = k + 1 ∨ k = m + 1 := by omega
  rcases this with rfl | rfl
  . use k, hk, k+1, hm; simp
  . use m, hm, m+1, hk; simp

import data.set.lattice
import data.set.function
import tactic

open set
open function

noncomputable theory
open_locale classical

variables {α β : Type*} [nonempty β]

section
variables (f : α → β) (g : β → α)

def sb_aux : ℕ → set α
| 0       := univ \ (g '' univ)
| (n + 1) := g '' (f '' sb_aux n)

def sb_set := ⋃ n, sb_aux f g n

def sb_fun (x : α) : β := if x ∈ sb_set f g then f x else inv_fun g x

theorem sb_right_inv {x : α} (hx : x ∉ sb_set f g) :
    g (inv_fun g x) = x :=
begin
  have : x ∈ g '' univ,
  { contrapose! hx,
    rw [sb_set, mem_Union],
    use [0],
    rw [sb_aux, mem_diff],
    exact ⟨mem_univ _, hx⟩ },
  have : ∃ y, g y = x,
  { simp at this, assumption },
  exact inv_fun_eq this
end

theorem sb_injective (hf: injective f) (hg : injective g) :
  injective (sb_fun f g) :=
begin
  set A := sb_set f g with A_def,
  set h := sb_fun f g with h_def,
  intros x₁ x₂,
  assume hxeq : h x₁ = h x₂,
  show x₁ = x₂,
  simp only [h_def, sb_fun, ←A_def] at hxeq,
  by_cases xA : x₁ ∈ A ∨ x₂ ∈ A,
  { wlog : x₁ ∈ A := xA using [x₁ x₂, x₂ x₁],
    have x₂A : x₂ ∈ A,
    { apply not_imp_self.mp,
      assume x₂nA : x₂ ∉ A,
      rw [if_pos xA, if_neg x₂nA] at hxeq,
      rw [A_def, sb_set, mem_Union] at xA,
      have x₂eq : x₂ = g (f x₁),
      { rw [hxeq, sb_right_inv f g x₂nA] },
      rcases xA with ⟨n, hn⟩,
      rw [A_def, sb_set, mem_Union],
      use n + 1,
      simp [sb_aux],
      exact ⟨x₁, hn, x₂eq.symm⟩ },
    rw [if_pos xA, if_pos x₂A] at hxeq,
    exact hf hxeq },
  push_neg at xA,
  rw [if_neg xA.1, if_neg xA.2] at hxeq,
  rw [←sb_right_inv f g xA.1, hxeq, sb_right_inv f g xA.2]
end

theorem sb_surjective (hf: injective f) (hg : injective g) :
  surjective (sb_fun f g) :=
begin
  set A := sb_set f g with A_def,
  set h := sb_fun f g with h_def,
  intro y,
  by_cases gyA : g y ∈ A,
  { rw [A_def, sb_set, mem_Union] at gyA,
    rcases gyA with ⟨n, hn⟩,
    cases n with n,
    { simp [sb_aux] at hn,
      contradiction },
    simp [sb_aux] at hn,
    rcases hn with ⟨x, xmem, hx⟩,
    use x,
    have : x ∈ A,
    { rw [A_def, sb_set, mem_Union],
      exact ⟨n, xmem⟩ },
    simp only [h_def, sb_fun, if_pos this],
    exact hg hx },
  use g y,
  simp only [h_def, sb_fun, if_neg gyA],
  apply left_inverse_inv_fun hg
end

end


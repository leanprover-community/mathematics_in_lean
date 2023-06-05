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
    sorry },
  have : ∃ y, g y = x,
  { sorry },
  sorry
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
      { sorry },
      rcases xA with ⟨n, hn⟩,
      rw [A_def, sb_set, mem_Union],
      use n + 1,
      simp [sb_aux],
      exact ⟨x₁, hn, x₂eq.symm⟩ },
    sorry },
  push_neg at xA,
  sorry
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
  sorry
end

end

theorem schroeder_bernstein {f : α → β} {g : β → α}
    (hf: injective f) (hg : injective g) :
  ∃ h : α → β, bijective h :=
⟨sb_fun f g, sb_injective f g hf hg, sb_surjective f g hf hg⟩

/- Auxliary information -/

section

variables  (g : β → α) (x : α)

#check (inv_fun g : α → β)

#check (left_inverse_inv_fun : injective g → left_inverse (inv_fun g) g)
#check (left_inverse_inv_fun : injective g → ∀ y, inv_fun g (g y) = y)

#check (inv_fun_eq : (∃ y, g y = x) → g (inv_fun g x) = x)
end

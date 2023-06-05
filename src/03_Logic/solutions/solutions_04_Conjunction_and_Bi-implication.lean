import data.real.basic
import data.nat.prime

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) :
  m ∣ n ∧ ¬ n ∣ m :=
begin
  cases h with h0 h1,
  split,
  { exact h0 },
  intro h2,
  apply h1,
  apply nat.dvd_antisymm h0 h2,
end

example {x y : ℝ} : x ≤ y ∧ ¬ y ≤ x ↔ x ≤ y ∧ x ≠ y :=
begin
  split,
  { rintros ⟨h0, h1⟩,
    split,
    { exact h0 },
    intro h2,
    apply h1,
    rw h2 },
  rintros ⟨h0, h1⟩,
  split,
  { exact h0 },
  intro h2,
  apply h1,
  apply le_antisymm h0 h2
end

theorem aux {x y : ℝ} (h : x^2 + y^2 = 0) : x = 0 :=
begin
  have h' : x^2 = 0,
  { linarith [pow_two_nonneg x, pow_two_nonneg y] },
  exact pow_eq_zero h'
end

example (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
begin
  split,
  { intro h,
    split,
    { exact aux h },
    rw add_comm at h,
    exact aux h },
  rintros ⟨rfl, rfl⟩,
  norm_num
end

theorem not_monotone_iff {f : ℝ → ℝ}:
  ¬ monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by { rw monotone, push_neg }

example : ¬ monotone (λ x : ℝ, -x) :=
begin
  rw not_monotone_iff,
  use [0, 1],
  norm_num
end

section
variables {α : Type*} [partial_order α]
variables a b : α

example : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  rw lt_iff_le_not_le,
  split,
  { rintros ⟨h0, h1⟩,
    split,
    { exact h0 },
    intro h2,
    apply h1,
    rw h2 },
  rintros ⟨h0, h1⟩,
  split,
  { exact h0 },
  intro h2,
  apply h1,
  apply le_antisymm h0 h2
end

end

section
variables {α : Type*} [preorder α]
variables a b c : α

example : ¬ a < a :=
begin
  rw lt_iff_le_not_le,
  rintros ⟨h0, h1⟩,
  exact h1 h0
end

example : a < b → b < c → a < c :=
begin
  simp only [lt_iff_le_not_le],
  rintros ⟨h0, h1⟩ ⟨h2, h3⟩,
  split,
  { apply le_trans h0 h2 },
  intro h4,
  apply h1,
  apply le_trans h2 h4
end

end

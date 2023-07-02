import data.real.basic

section
variables {x y : ℝ}

namespace my_abs

theorem le_abs_self (x : ℝ) : x ≤ abs x :=
begin
  cases le_or_gt 0 x with h h,
  { rw abs_of_nonneg h },
  rw abs_of_neg h,
  linarith
end

theorem neg_le_abs_self (x : ℝ) : -x ≤ abs x :=
begin
  cases le_or_gt 0 x with h h,
  { rw abs_of_nonneg h,
    linarith },
  rw abs_of_neg h
end

theorem abs_add (x y : ℝ) : abs (x + y) ≤ abs x + abs y :=
begin
  cases le_or_gt 0 (x + y) with h h,
  { rw abs_of_nonneg h,
    linarith [le_abs_self x, le_abs_self y] },
  rw abs_of_neg h,
  linarith [neg_le_abs_self x, neg_le_abs_self y]
end

theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with h h,
  { rw abs_of_nonneg h,
    split,
    { intro h', left, exact h' },
    intro h',
    cases h' with h' h',
    { exact h' },
    linarith },
  rw abs_of_neg h,
  split,
  { intro h', right, exact h' },
  intro h',
  cases h' with h' h',
  { linarith },
  exact h'
end

theorem abs_lt : abs x < y ↔ - y < x ∧ x < y :=
begin
  cases le_or_gt 0 x with h h,
  { rw abs_of_nonneg h,
    split,
    { intro h',
      split,
      { linarith },
      exact h' },
    intro h',
    cases h' with h1 h2,
    exact h2 },
  rw abs_of_neg h,
  split,
  { intro h',
    split,
    { linarith },
    linarith },
  intro h',
  linarith
end

end my_abs
end

example {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
  z ≥ 0 :=
by { rcases h with ⟨x, y, rfl | rfl⟩; linarith [sq_nonneg x, sq_nonneg y] }

example {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 :=
begin
  have h' : x^2 - 1 = 0,
  { rw [h, sub_self] },
  have h'' : (x + 1) * (x - 1) = 0,
  { rw ← h',
    ring },
  cases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 h1,
  { right,
    exact eq_neg_iff_add_eq_zero.mpr h1 },
  left,
  exact eq_of_sub_eq_zero h1
end

example {x y : ℝ} (h : x^2 = y^2) : x = y ∨ x = -y :=
begin
  have h' : x^2 - y^2 = 0,
  { rw [h, sub_self] },
  have h'' : (x + y) * (x - y) = 0,
  { rw ← h',
    ring },
  cases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 h1,
  { right,
    exact eq_neg_iff_add_eq_zero.mpr h1 },
  left,
  exact eq_of_sub_eq_zero h1
end

section
variables {R : Type*} [comm_ring R] [is_domain R]
variables (x y : R)

example (h : x^2 = 1) : x = 1 ∨ x = -1 :=
begin
  have h' : x^2 - 1 = 0,
  { rw [h, sub_self] },
  have h'' : (x + 1) * (x - 1) = 0,
  { rw ← h',
    ring },
  cases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 h1,
  { right,
    exact eq_neg_iff_add_eq_zero.mpr h1 },
  left,
  exact eq_of_sub_eq_zero h1
end

example (h : x^2 = y^2) : x = y ∨ x = -y :=
begin
  have h' : x^2 - y^2 = 0,
  { rw [h, sub_self] },
  have h'' : (x + y) * (x - y) = 0,
  { rw ← h',
    ring },
  cases eq_zero_or_eq_zero_of_mul_eq_zero h'' with h1 h1,
  { right,
    exact eq_neg_iff_add_eq_zero.mpr h1 },
  left,
  exact eq_of_sub_eq_zero h1
end

end

section
open_locale classical

example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
begin
  split,
  { intro h,
    by_cases h' : P,
    { right,
      exact h h'},
    left,
    exact h' },
  rintros (h | h),
  { intro h',
    exact absurd h' h },
  intro _,
  exact h
end

end
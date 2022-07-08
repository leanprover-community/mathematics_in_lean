import data.int.basic
import ring_theory.principal_ideal_domain
import tactic

@[ext] structure gaussint := (re : ℤ) (im : ℤ)

namespace gaussint

instance : has_zero gaussint := ⟨⟨0, 0⟩⟩
instance : has_one gaussint  := ⟨⟨1, 0⟩⟩
instance : has_add gaussint  := ⟨λ x y, ⟨x.re + y.re, x.im + y.im⟩⟩
instance : has_neg gaussint  := ⟨λ x, ⟨-x.re, -x.im⟩⟩
instance : has_mul gaussint  :=
  ⟨λ x y, ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

theorem zero_def : (0 : gaussint) = ⟨0, 0⟩ := rfl
theorem one_def : (1 : gaussint) = ⟨1, 0⟩ := rfl
theorem add_def (x y : gaussint) : x + y = ⟨x.re + y.re, x.im + y.im⟩ := rfl
theorem neg_def (x : gaussint) : -x = ⟨-x.re, -x.im⟩ := rfl
theorem mul_def (x y : gaussint) :
  x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ := rfl

@[simp] theorem zero_re : (0 : gaussint).re = 0 := rfl
@[simp] theorem zero_im : (0 : gaussint).im = 0 := rfl
@[simp] theorem one_re : (1 : gaussint).re = 1 := rfl
@[simp] theorem one_im : (1 : gaussint).im = 0 := rfl
@[simp] theorem add_re (x y : gaussint) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : gaussint) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : gaussint) : (-x).re = - x.re := rfl
@[simp] theorem neg_im (x : gaussint) : (-x).im = - x.im := rfl
@[simp] theorem mul_re (x y : gaussint) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem mul_im (x y : gaussint) : (x * y).im = x.re * y.im + x.im * y.re := rfl

instance : comm_ring gaussint :=
{ zero := 0,
  one := 1,
  add := (+),
  neg := λ x, -x,
  mul := (*),

  add_assoc := by { intros, ext; simp; ring },
  zero_add := by { intros, ext; simp },
  add_zero := by { intros, ext; simp },
  add_left_neg := by { intros, ext; simp },
  add_comm := by { intros, ext; simp; ring },
  mul_assoc := by { intros, ext; simp; ring },
  one_mul := by { intros, ext; simp },
  mul_one := by { intros, ext; simp },
  left_distrib := by { intros, ext; simp; ring },
  right_distrib := by { intros, ext; simp; ring },
  mul_comm := by { intros, ext; simp; ring } }

instance : nontrivial gaussint :=
by { use [0, 1], rw [ne, gaussint.ext_iff], simp }

end gaussint

namespace int

def div' (a b : ℤ) := (a + b / 2) / b

def mod' (a b : ℤ) := (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a :=
begin
  rw [div', mod'],
  linarith [int.div_add_mod (a + b / 2) b],
end

theorem abs_mod'_le (a b : ℤ) (h : 0 < b): abs (mod' a b) ≤ b / 2 :=
begin
  rw [mod', abs_le],
  split,
  { linarith [int.mod_nonneg (a + b / 2) h.ne'] },
  have := int.mod_lt_of_pos (a + b / 2) h,
  have := int.div_add_mod b 2,
  have := int.mod_lt_of_pos b zero_lt_two,
  linarith
end

theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b :=
by linarith [div'_add_mod' a b]

end int

private theorem aux {α : Type*} [linear_ordered_ring α] {x y : α} (h : x^2 + y^2 = 0) : x = 0 :=
begin
  have h' : x^2 = 0,
  { apply le_antisymm _ (sq_nonneg x),
    rw ←h,
    apply le_add_of_nonneg_right (sq_nonneg y) },
  exact pow_eq_zero h'
end

theorem sq_add_sq_eq_zero {α : Type*} [linear_ordered_ring α] (x y : α) :
  x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 :=
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

namespace gaussint

def norm (x : gaussint) := x.re^2 + x.im^2

@[simp] theorem norm_nonneg (x : gaussint) : 0 ≤ norm x :=
by { apply add_nonneg; apply sq_nonneg }

theorem norm_eq_zero (x : gaussint) : norm x = 0 ↔ x = 0 :=
by { rw [norm, sq_add_sq_eq_zero, gaussint.ext_iff], refl }

theorem norm_pos (x : gaussint) : 0 < norm x ↔ x ≠ 0 :=
by { rw [lt_iff_le_and_ne, ne_comm, ne, norm_eq_zero], simp [norm_nonneg] }

theorem norm_mul (x y : gaussint) : norm (x * y) = norm x * norm y :=
by { simp [norm], ring }

def conj (x : gaussint) : gaussint := ⟨x.re, -x.im⟩

@[simp] theorem conj_re (x : gaussint) : (conj x).re = x.re := rfl
@[simp] theorem conj_im (x : gaussint) : (conj x).im = - x.im := rfl

theorem norm_conj (x : gaussint) : norm (conj x) = norm x :=
by { simp [norm] }

instance : has_div gaussint :=
⟨λ x y, ⟨int.div' (x * conj y).re (norm y), int.div' (x * conj y).im (norm y)⟩⟩

instance : has_mod gaussint := ⟨λ x y, x - y * (x / y)⟩

theorem div_def (x y : gaussint) :
  x / y = ⟨int.div' (x * conj y).re (norm y), int.div' (x * conj y).im (norm y)⟩ := rfl

theorem mod_def (x y : gaussint) : x % y = x - y * (x / y) := rfl

lemma norm_mod_lt (x : gaussint) {y : gaussint} (hy : y ≠ 0) : (x % y).norm < y.norm :=
begin
  have norm_y_pos : 0 < norm y,
    by rwa [norm_pos],
  have : (x % y) * conj y =
    ⟨int.mod' (x * conj y).re (norm y), int.mod' (x * conj y).im (norm y)⟩,
  { rw [mod_def, sub_mul, int.mod'_eq, int.mod'_eq, sub_eq_add_neg, norm, div_def],
    ext; simp; ring },
  have : norm (x % y) * norm y ≤ (norm y / 2) * norm y,
  { conv { to_lhs, rw [←norm_conj y, ←norm_mul, this, norm] },
    simp,
    transitivity 2 * (y.norm / 2)^2,
    { rw [two_mul],
      apply add_le_add;
      { rw [sq_le_sq],
        apply le_trans (int.abs_mod'_le _ _ norm_y_pos),
        apply le_abs_self } },
      rw [pow_two, ←mul_assoc, mul_comm, mul_comm (2 : ℤ)],
      apply mul_le_mul_of_nonneg_left _ _,
      { apply int.div_mul_le, norm_num },
      apply int.div_nonneg (norm_nonneg y), norm_num },
  have : norm (x % y) ≤ norm y / 2 := le_of_mul_le_mul_right this norm_y_pos,
  apply lt_of_le_of_lt this,
  apply int.div_lt_of_lt_mul, { norm_num },
  linarith
end

lemma coe_nat_abs_norm (x : gaussint) : (x.norm.nat_abs : ℤ) = x.norm :=
int.nat_abs_of_nonneg (norm_nonneg _)

lemma nat_abs_norm_mod_lt (x y : gaussint) (hy : y ≠ 0) :
  (x % y).norm.nat_abs < y.norm.nat_abs :=
begin
  apply int.coe_nat_lt.1, simp,
  exact int.nat_abs_lt_nat_abs_of_nonneg_of_lt (norm_nonneg _) (norm_mod_lt x hy)
end

lemma not_norm_mul_left_lt_norm (x : gaussint) {y : gaussint} (hy : y ≠ 0) :
  ¬ (norm (x * y)).nat_abs < (norm x).nat_abs :=
begin
  apply not_lt_of_ge,
  rw [norm_mul, int.nat_abs_mul],
  apply le_mul_of_one_le_right (nat.zero_le _),
  apply int.coe_nat_le.1,
  rw [coe_nat_abs_norm],
  exact int.add_one_le_of_lt ((norm_pos _).mpr hy)
end

instance : euclidean_domain gaussint :=
{ quotient        := (/),
  remainder       := (%),
  quotient_mul_add_remainder_eq :=
                     λ x y, by {rw [mod_def, add_comm, sub_add_cancel] },
  quotient_zero   := λ x, by { simp [div_def, norm, int.div'], refl },
  r               := measure (int.nat_abs ∘ norm),
  r_well_founded  := measure_wf (int.nat_abs ∘ norm),
  remainder_lt    := nat_abs_norm_mod_lt,
  mul_left_not_lt := not_norm_mul_left_lt_norm,
  .. gaussint.comm_ring }

example (x : gaussint) : irreducible x ↔ prime x :=
principal_ideal_ring.irreducible_iff_prime

end gaussint


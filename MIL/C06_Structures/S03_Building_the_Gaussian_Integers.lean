import Mathlib.Data.Int.Basic
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import MIL.Common

@[ext]
structure gaussInt where
  re : ℤ
  im : ℤ

namespace gaussInt

instance : Zero gaussInt :=
  ⟨⟨0, 0⟩⟩

instance : One gaussInt :=
  ⟨⟨1, 0⟩⟩

instance : Add gaussInt :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg gaussInt :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

instance : Mul gaussInt :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

theorem zero_def : (0 : gaussInt) = ⟨0, 0⟩ :=
  rfl

theorem one_def : (1 : gaussInt) = ⟨1, 0⟩ :=
  rfl

theorem add_def (x y : gaussInt) : x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
  rfl

theorem neg_def (x : gaussInt) : -x = ⟨-x.re, -x.im⟩ :=
  rfl

theorem mul_def (x y : gaussInt) :
    x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
  rfl

@[simp]
theorem zero_re : (0 : gaussInt).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : gaussInt).im = 0 :=
  rfl

@[simp]
theorem one_re : (1 : gaussInt).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : gaussInt).im = 0 :=
  rfl

@[simp]
theorem add_re (x y : gaussInt) : (x + y).re = x.re + y.re :=
  rfl

@[simp]
theorem add_im (x y : gaussInt) : (x + y).im = x.im + y.im :=
  rfl

@[simp]
theorem neg_re (x : gaussInt) : (-x).re = -x.re :=
  rfl

@[simp]
theorem neg_im (x : gaussInt) : (-x).im = -x.im :=
  rfl

@[simp]
theorem mul_re (x y : gaussInt) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp]
theorem mul_im (x y : gaussInt) : (x * y).im = x.re * y.im + x.im * y.re :=
  rfl

instance instCommRing : CommRing gaussInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  add_assoc := by
    intros
    ext <;> simp <;> ring
  zero_add := by
    intro
    ext <;> simp
  add_zero := by
    intro
    ext <;> simp
  add_left_neg := by
    intro
    ext <;> simp
  add_comm := by
    intros
    ext <;> simp <;> ring
  mul_assoc := by
    intros
    ext <;> simp <;> ring
  one_mul := by
    intro
    ext <;> simp
  mul_one := by
    intro
    ext <;> simp
  left_distrib := by
    intros
    ext <;> simp <;> ring
  right_distrib := by
    intros
    ext <;> simp <;> ring
  mul_comm := by
    intros
    ext <;> simp <;> ring
  zero_mul := sorry
  mul_zero := sorry

@[simp]
theorem sub_re (x y : gaussInt) : (x - y).re = x.re - y.re :=
  rfl

@[simp]
theorem sub_im (x y : gaussInt) : (x - y).im = x.im - y.im :=
  rfl

instance : Nontrivial gaussInt := by
  use 0, 1
  rw [Ne, gaussInt.ext_iff]
  simp

end gaussInt

example (a b : ℤ) : a = b * (a / b) + a % b :=
  Eq.symm (Int.ediv_add_emod a b)

example (a b : ℤ) : b ≠ 0 → 0 ≤ a % b :=
  Int.emod_nonneg a

example (a b : ℤ) : b ≠ 0 → a % b < |b| :=
  Int.emod_lt a

namespace Int

def div' (a b : ℤ) :=
  (a + b / 2) / b

def mod' (a b : ℤ) :=
  (a + b / 2) % b - b / 2

theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a := by
  rw [div', mod']
  linarith [Int.ediv_add_emod (a + b / 2) b]

theorem abs_mod'_le (a b : ℤ) (h : 0 < b) : |mod' a b| ≤ b / 2 := by
  rw [mod', abs_le]
  constructor
  · linarith [Int.emod_nonneg (a + b / 2) h.ne']
  have := Int.emod_lt_of_pos (a + b / 2) h
  have := Int.ediv_add_emod b 2
  have := Int.emod_lt_of_pos b zero_lt_two
  revert this; intro this -- FIXME, this should not be needed
  linarith

theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b := by linarith [div'_add_mod' a b]

end Int

theorem sq_add_sq_eq_zero {α : Type*} [LinearOrderedRing α] (x y : α) :
    x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  sorry
namespace gaussInt

def norm (x : gaussInt) :=
  x.re ^ 2 + x.im ^ 2

@[simp]
theorem norm_nonneg (x : gaussInt) : 0 ≤ norm x := by
  sorry
theorem norm_eq_zero (x : gaussInt) : norm x = 0 ↔ x = 0 := by
  sorry
theorem norm_pos (x : gaussInt) : 0 < norm x ↔ x ≠ 0 := by
  sorry
theorem norm_mul (x y : gaussInt) : norm (x * y) = norm x * norm y := by
  sorry
def conj (x : gaussInt) : gaussInt :=
  ⟨x.re, -x.im⟩

@[simp]
theorem conj_re (x : gaussInt) : (conj x).re = x.re :=
  rfl

@[simp]
theorem conj_im (x : gaussInt) : (conj x).im = -x.im :=
  rfl

theorem norm_conj (x : gaussInt) : norm (conj x) = norm x := by simp [norm]

instance : Div gaussInt :=
  ⟨fun x y ↦ ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩⟩

instance : Mod gaussInt :=
  ⟨fun x y ↦ x - y * (x / y)⟩

theorem div_def (x y : gaussInt) :
    x / y = ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩ :=
  rfl

theorem mod_def (x y : gaussInt) : x % y = x - y * (x / y) :=
  rfl

theorem norm_mod_lt (x : gaussInt) {y : gaussInt} (hy : y ≠ 0) :
    (x % y).norm < y.norm := by
  have norm_y_pos : 0 < norm y := by rwa [norm_pos]
  have H1 : x % y * conj y = ⟨Int.mod' (x * conj y).re (norm y), Int.mod' (x * conj y).im (norm y)⟩
  · ext <;> simp [Int.mod'_eq, mod_def, div_def, norm] <;> ring
  have H2 : norm (x % y) * norm y ≤ norm y / 2 * norm y
  · calc
      norm (x % y) * norm y = norm (x % y * conj y) := by simp only [norm_mul, norm_conj]
      _ = |Int.mod' (x.re * y.re + x.im * y.im) (norm y)| ^ 2
          + |Int.mod' (-(x.re * y.im) + x.im * y.re) (norm y)| ^ 2 := by simp [H1, norm, sq_abs]
      _ ≤ (y.norm / 2) ^ 2 + (y.norm / 2) ^ 2 := by gcongr <;> apply Int.abs_mod'_le _ _ norm_y_pos
      _ = norm y / 2 * (norm y / 2 * 2) := by ring
      _ ≤ norm y / 2 * norm y := by gcongr; apply Int.ediv_mul_le; norm_num
  calc norm (x % y) ≤ norm y / 2 := le_of_mul_le_mul_right H2 norm_y_pos
    _ < norm y := by
        apply Int.ediv_lt_of_lt_mul
        · norm_num
        · linarith

theorem coe_natAbs_norm (x : gaussInt) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)

theorem natAbs_norm_mod_lt (x y : gaussInt) (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  apply Int.ofNat_lt.1
  simp only [Int.coe_natAbs, abs_of_nonneg, norm_nonneg]
  apply norm_mod_lt x hy

theorem not_norm_mul_left_lt_norm (x : gaussInt) {y : gaussInt} (hy : y ≠ 0) :
    ¬(norm (x * y)).natAbs < (norm x).natAbs := by
  apply not_lt_of_ge
  rw [norm_mul, Int.natAbs_mul]
  apply le_mul_of_one_le_right (Nat.zero_le _)
  apply Int.ofNat_le.1
  rw [coe_natAbs_norm]
  exact Int.add_one_le_of_lt ((norm_pos _).mpr hy)

instance : EuclideanDomain gaussInt :=
  { gaussInt.instCommRing with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_mul_add_remainder_eq :=
      fun x y ↦ by simp only; rw [mod_def, add_comm, sub_add_cancel]
    quotient_zero := fun x ↦ by
      simp [div_def, norm, Int.div']
      rfl
    r := (measure (Int.natAbs ∘ norm)).1
    r_wellFounded := (measure (Int.natAbs ∘ norm)).2
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := not_norm_mul_left_lt_norm }

example (x : gaussInt) : Irreducible x ↔ Prime x :=
  PrincipalIdealRing.irreducible_iff_prime

end gaussInt

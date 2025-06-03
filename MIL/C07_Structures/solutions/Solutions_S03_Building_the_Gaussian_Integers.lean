import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import MIL.Common

@[ext]
structure GaussInt where
  re : ℤ
  im : ℤ

namespace GaussInt

instance : Zero GaussInt :=
  ⟨⟨0, 0⟩⟩

instance : One GaussInt :=
  ⟨⟨1, 0⟩⟩

instance : Add GaussInt :=
  ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

instance : Neg GaussInt :=
  ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

instance : Mul GaussInt :=
  ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

theorem zero_def : (0 : GaussInt) = ⟨0, 0⟩ :=
  rfl

theorem one_def : (1 : GaussInt) = ⟨1, 0⟩ :=
  rfl

theorem add_def (x y : GaussInt) : x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
  rfl

theorem neg_def (x : GaussInt) : -x = ⟨-x.re, -x.im⟩ :=
  rfl

theorem mul_def (x y : GaussInt) :
    x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
  rfl

@[simp]
theorem zero_re : (0 : GaussInt).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem one_re : (1 : GaussInt).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : GaussInt).im = 0 :=
  rfl

@[simp]
theorem add_re (x y : GaussInt) : (x + y).re = x.re + y.re :=
  rfl

@[simp]
theorem add_im (x y : GaussInt) : (x + y).im = x.im + y.im :=
  rfl

@[simp]
theorem neg_re (x : GaussInt) : (-x).re = -x.re :=
  rfl

@[simp]
theorem neg_im (x : GaussInt) : (-x).im = -x.im :=
  rfl

@[simp]
theorem mul_re (x y : GaussInt) : (x * y).re = x.re * y.re - x.im * y.im :=
  rfl

@[simp]
theorem mul_im (x y : GaussInt) : (x * y).im = x.re * y.im + x.im * y.re :=
  rfl

instance instCommRing : CommRing GaussInt where
  zero := 0
  one := 1
  add := (· + ·)
  neg x := -x
  mul := (· * ·)
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by
    intros
    ext <;> simp <;> ring
  zero_add := by
    intro
    ext <;> simp
  add_zero := by
    intro
    ext <;> simp
  neg_add_cancel := by
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
  zero_mul := by
    intros
    ext <;> simp
  mul_zero := by
    intros
    ext <;> simp

@[simp]
theorem sub_re (x y : GaussInt) : (x - y).re = x.re - y.re :=
  rfl

@[simp]
theorem sub_im (x y : GaussInt) : (x - y).im = x.im - y.im :=
  rfl

instance : Nontrivial GaussInt := by
  use 0, 1
  rw [Ne, GaussInt.ext_iff]
  simp

end GaussInt

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
  linarith

theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b := by linarith [div'_add_mod' a b]

end Int

private theorem aux {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {x y : α} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  haveI h' : x ^ 2 = 0 := by
    apply le_antisymm _ (sq_nonneg x)
    rw [← h]
    apply le_add_of_nonneg_right (sq_nonneg y)
  pow_eq_zero h'

theorem sq_add_sq_eq_zero {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
    (x y : α) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · exact aux h
    rw [add_comm] at h
    exact aux h
  rintro ⟨rfl, rfl⟩
  norm_num

namespace GaussInt

def norm (x : GaussInt) :=
  x.re ^ 2 + x.im ^ 2

@[simp]
theorem norm_nonneg (x : GaussInt) : 0 ≤ norm x := by
  apply add_nonneg <;>
  apply sq_nonneg

theorem norm_eq_zero (x : GaussInt) : norm x = 0 ↔ x = 0 := by
  rw [norm, sq_add_sq_eq_zero, GaussInt.ext_iff]
  rfl

theorem norm_pos (x : GaussInt) : 0 < norm x ↔ x ≠ 0 := by
  rw [lt_iff_le_and_ne, ne_comm, Ne, norm_eq_zero]
  simp [norm_nonneg]

theorem norm_mul (x y : GaussInt) : norm (x * y) = norm x * norm y := by
  simp [norm]
  ring

def conj (x : GaussInt) : GaussInt :=
  ⟨x.re, -x.im⟩

@[simp]
theorem conj_re (x : GaussInt) : (conj x).re = x.re :=
  rfl

@[simp]
theorem conj_im (x : GaussInt) : (conj x).im = -x.im :=
  rfl

theorem norm_conj (x : GaussInt) : norm (conj x) = norm x := by simp [norm]

instance : Div GaussInt :=
  ⟨fun x y ↦ ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩⟩

instance : Mod GaussInt :=
  ⟨fun x y ↦ x - y * (x / y)⟩

theorem div_def (x y : GaussInt) :
    x / y = ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩ :=
  rfl

theorem mod_def (x y : GaussInt) : x % y = x - y * (x / y) :=
  rfl

theorem norm_mod_lt (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
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

theorem coe_natAbs_norm (x : GaussInt) : (x.norm.natAbs : ℤ) = x.norm :=
  Int.natAbs_of_nonneg (norm_nonneg _)

theorem natAbs_norm_mod_lt (x y : GaussInt) (hy : y ≠ 0) :
    (x % y).norm.natAbs < y.norm.natAbs := by
  apply Int.ofNat_lt.1
  simp only [Int.natCast_natAbs, abs_of_nonneg, norm_nonneg]
  exact norm_mod_lt x hy

theorem not_norm_mul_left_lt_norm (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
    ¬(norm (x * y)).natAbs < (norm x).natAbs := by
  apply not_lt_of_ge
  rw [norm_mul, Int.natAbs_mul]
  apply le_mul_of_one_le_right (Nat.zero_le _)
  apply Int.ofNat_le.1
  rw [coe_natAbs_norm]
  exact Int.add_one_le_of_lt ((norm_pos _).mpr hy)

instance : EuclideanDomain GaussInt :=
  { GaussInt.instCommRing with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_mul_add_remainder_eq :=
      fun x y ↦ by rw [mod_def, add_comm] ; ring
    quotient_zero := fun x ↦ by
      simp [div_def, norm, Int.div']
      rfl
    r := (measure (Int.natAbs ∘ norm)).1
    r_wellFounded := (measure (Int.natAbs ∘ norm)).2
    remainder_lt := natAbs_norm_mod_lt
    mul_left_not_lt := not_norm_mul_left_lt_norm }

example (x : GaussInt) : Irreducible x ↔ Prime x :=
  irreducible_iff_prime

end GaussInt

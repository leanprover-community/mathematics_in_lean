import Mathlib.Data.Real.Basic

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

example : (fun x y : ℝ => (x + y) ^ 2) = fun x y : ℝ => x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : abs a = abs (a - b + b) := by
  congr
  ring

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert(mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ => a) a := by
  intro ε εpos
  use 0
  intro n nge; dsimp
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n => s n + t n) (a + b) := by
  intro ε εpos
  dsimp
  have ε2pos : 0 < ε / 2 := by linarith
  cases' cs (ε / 2) ε2pos with Ns hs
  cases' ct (ε / 2) ε2pos with Nt ht
  use max Ns Nt
  sorry

theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n => c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h, MulZeroClass.zero_mul]
    rw [h, MulZeroClass.zero_mul]
  have acpos : 0 < abs c := abs_pos.mpr h
  sorry

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → abs (s n) < b := by
  cases' cs 1 zero_lt_one with N h
  use N, abs a + 1
  sorry

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n => s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  cases' ct _ pos₀ with N₁ h₁
  sorry

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n => s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n => s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ} (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : abs (a - b) > 0 := by sorry
  let ε := abs (a - b) / 2
  have εpos : ε > 0 := by
    change abs (a - b) / 2 > 0
    linarith
  cases' sa ε εpos with Na hNa
  cases' sb ε εpos with Nb hNb
  let N := max Na Nb
  have absa : abs (s N - a) < ε := by sorry
  have absb : abs (s N - b) < ε := by sorry
  have : abs (a - b) < abs (a - b) := by sorry
  exact lt_irrefl _ this

section

variable {α : Type _} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

end


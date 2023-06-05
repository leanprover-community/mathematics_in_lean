import Mathlib.Data.Real.Basic

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩

example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

theorem fnUb_add {f g : ℝ → ℝ} {a b : ℝ} (hfa : FnUb f a) (hgb : FnUb g b) :
    FnUb (fun x => f x + g x) (a + b) :=
  fun x => add_le_add (hfa x) (hgb x)

section

variable {f g : ℝ → ℝ}

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x => f x + g x := by
  cases' ubf with a ubfa
  cases' ubg with b ubfb
  use a + b
  apply fnUb_add ubfa ubfb

example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x => f x + g x := by
  sorry

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x => c * f x := by
  sorry

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x => f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubfb⟩
  exact ⟨a + b, fnUb_add ubfa ubfb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x => f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubfb⟩
  exact ⟨a + b, fnUb_add ubfa ubfb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x => f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubfb⟩ => ⟨a + b, fnUb_add ubfa ubfb⟩

end

section

variable {α : Type _} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring

theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring

end

section

variable {a b c : ℕ}

example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  cases' divab with d beq
  cases' divbc with e ceq
  rw [ceq, beq]
  use d * e; ring

example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  sorry

end

section

open Function

example {c : ℝ} : Surjective fun x => x + c := by
  intro x
  use x - c
  dsimp; ring

example {c : ℝ} (h : c ≠ 0) : Surjective fun x => c * x := by
  sorry

example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring

example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  cases' h 2 with x hx
  use x
  rw [hx]
  norm_num

end

section

open Function

variable {α : Type _} {β : Type _} {γ : Type _}

variable {g : β → γ} {f : α → β}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x => g (f x) := by
  sorry

end


import data.real.basic

section
variables {x y : ℝ}

example (h : y > x^2) : y > 0 ∨ y < -1 :=
by { left, linarith [pow_two_nonneg x] }

example (h : -y > x^2 + 1) : y > 0 ∨ y < -1 :=
by { right, linarith [pow_two_nonneg x] }

example (h : y > 0) : y > 0 ∨ y < -1 :=
or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
or.inr h

example : x < abs y → x < y ∨ x < -y :=
begin
  cases le_or_gt 0 y with h h,
  { rw abs_of_nonneg h,
    intro h, left, exact h },
  rw abs_of_neg h,
  intro h, right, exact h
end

namespace my_abs

theorem le_abs_self (x : ℝ) : x ≤ abs x := begin
  cases le_or_gt 0 x with h h,
  { show x ≤ |x|, -- 0 ≤ x
    rw abs_of_nonneg h,
  },
  { show x ≤ |x|,
    rw abs_of_neg h,
    linarith,
  },
end

theorem neg_le_abs_self (x : ℝ) : -x ≤ abs x := begin
  cases le_or_gt 0 x with h h,
  { show -x ≤ |x|, -- 0 ≤ x
    rw abs_of_nonneg h,
    linarith,
  },
  { show -x ≤ |x|, -- 0 < x
    rw abs_of_neg h,
  },
end

-- 아래 3개에서 lt_abs, abs_lt를 사용하기
theorem abs_add (x y : ℝ) : abs (x + y) ≤ abs x + abs y := begin

  apply le_of_lt_or_eq,
  cases lt_trichotomy x 0 with xlt0 xgeq0,
  { -- xlt0
    rw abs_of_neg xlt0,
    cases le_or_gt y 0 with yle0 ygt0,
    { -- xlt0 ∧ yle0
      right,
      rw abs_of_nonpos yle0,
      rw abs_of_nonpos,
      by linarith,
      by linarith,
    },
    { -- xlt0 ∧ ygt0
      left,
      rw abs_of_pos ygt0,
      apply abs_lt.mpr,
      have h0: -(-x + y) < x + y, linarith,
      have h1: x + y < -x + y, linarith,
      exact ⟨ h0, h1 ⟩,
      exact has_add.to_covariant_class_left ℝ,
      exact has_add.to_covariant_class_right ℝ,
    }
  },
  cases xgeq0 with xeq0 xgt0,
  {  -- xeq0
    rw xeq0,
    rw zero_add,
    rw abs_zero,
    rw zero_add,
    right,
    exact rfl,
  },
  { -- xgt0
    cases le_or_gt 0 y with yge0 ylt0,
    { -- xgt 0 ∧ yge0
      right,
      rw [(abs_of_pos xgt0), (abs_of_nonneg yge0), (abs_of_pos) ],
      linarith,
    },
    { -- xgt 0 ∧ ylt0
      left,
      rw [abs_of_pos xgt0, abs_of_neg ylt0],
      apply abs_lt.mpr,
      have z0: -(x + -y) < x + y, by linarith,
      have z1: x + y < x + -y, by linarith,
      exact ⟨ z0, z1 ⟩,
      
      exact has_add.to_covariant_class_left ℝ,
      exact has_add.to_covariant_class_right ℝ,
    },
  },
end

theorem lt_abs : x < abs y ↔ x < y ∨ x < -y :=
sorry

theorem abs_lt : abs x < y ↔ - y < x ∧ x < y :=
sorry

end my_abs
end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 :=
begin
  rcases lt_trichotomy x 0 with xlt | xeq | xgt,
  { left, exact xlt },
  { contradiction },
  right, exact xgt
end

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k :=
begin
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩,
  { rw [mul_assoc],
    apply dvd_mul_right },
  rw [mul_comm, mul_assoc],
  apply dvd_mul_right
end

example {z : ℝ} (h : ∃ x y, z = x^2 + y^2 ∨ z = x^2 + y^2 + 1) :
  z ≥ 0 :=
sorry

example {x : ℝ} (h : x^2 = 1) : x = 1 ∨ x = -1 :=
sorry

example {x y : ℝ} (h : x^2 = y^2) : x = y ∨ x = -y :=
sorry

section
variables {R : Type*} [comm_ring R] [is_domain R]
variables (x y : R)

example (h : x^2 = 1) : x = 1 ∨ x = -1 :=
sorry

example (h : x^2 = y^2) : x = y ∨ x = -y :=
sorry

end

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  cases classical.em P,
  { assumption },
  contradiction
end

section
open_locale classical

example (P : Prop) : ¬ ¬ P → P :=
begin
  intro h,
  by_cases h' : P,
  { assumption },
  contradiction
end

example (P Q : Prop) : (P → Q) ↔ ¬ P ∨ Q :=
sorry

end
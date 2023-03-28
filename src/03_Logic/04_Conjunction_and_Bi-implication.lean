import data.real.basic
import data.nat.prime

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  split,
  { assumption },
  intro h,
  apply h₁,
  rw h,
end

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
⟨h₀, λ h, h₁ (by rw h)⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
begin
  have h : x ≠ y,
  { contrapose! h₁,
    rw h₁ },
  exact ⟨h₀, h⟩
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  cases h with h₀ h₁,
  contrapose! h₁,
  exact le_antisymm h₀ h₁
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
begin
  rintros ⟨h₀, h₁⟩ h',
  exact h₁ (le_antisymm h₀ h')
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬ y ≤ x :=
λ ⟨h₀, h₁⟩ h', h₁ (le_antisymm h₀ h')

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
begin
  intro h',
  apply h.right,
  exact le_antisymm h.left h'
end

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬ y ≤ x :=
λ h', h.right (le_antisymm h.left h')

example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) :
  m ∣ n ∧ ¬ n ∣ m := begin
  split,
  { exact h.left },
  { show ¬ n ∣ m,
    contrapose! h,
    intro nm,
    exact nat.dvd_antisymm nm h,
  },
end

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
⟨5/2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
begin
  rintros ⟨z, xltz, zlty⟩,
  exact lt_trans xltz zlty
end

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
λ ⟨z, xltz, zlty⟩, lt_trans xltz zlty

example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
begin
  use 5 / 2,
  split; norm_num
end

example : ∃ m n : ℕ,
  4 < m ∧ m < n ∧ n < 10 ∧ nat.prime m ∧ nat.prime n :=
begin
  use [5, 7],
  norm_num
end

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬ y ≤ x :=
begin
  rintros ⟨h₀, h₁⟩,
  use [h₀, λ h', h₁ (le_antisymm h₀ h')]
end

example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
begin
  split,
  { contrapose!,
    rintro rfl,
    reflexivity },
  contrapose!,
  exact le_antisymm h
end

example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y :=
⟨λ h₀ h₁, h₀ (by rw h₁), λ h₀ h₁, h₀ (le_antisymm h h₁)⟩

example {x y : ℝ} : x ≤ y ∧ ¬ y ≤ x ↔ x ≤ y ∧ x ≠ y :=
begin
split,
{ show x ≤ y ∧ ¬y ≤ x → x ≤ y ∧ x ≠ y,
  rintros ⟨ xlty, nyltx⟩,
  split,
  { show x ≤ y,
    exact xlty },
  { show x ≠ y,
    contrapose! nyltx,
    linarith,
  }
},
{ show x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x,
  rintros ⟨ xlty, nyltx ⟩,
  split,
  { show x ≤ y,
    exact xlty },
  { show ¬y ≤ x,
    contrapose! nyltx,
    linarith,
  }
},
end

theorem aux {x y : ℝ} (h : x^2 + y^2 = 0) : x = 0 :=
begin
  have h' : x^2 = 0,
  { 
    have y2gezero : y^2 ≥ 0,
    { exact sq_nonneg y,},
    have x2gezero : x^2 ≥ 0,
    { exact sq_nonneg x },
    linarith,
   },
  exact pow_eq_zero h'
end

example (x y : ℝ) : x^2 + y^2 = 0 ↔ x = 0 ∧ y = 0 := begin
  split,
  { show x ^ 2 + y ^ 2 = 0 → x = 0 ∧ y = 0,
    intros x2py2eq0,
    have xsqgte0 : x^2 ≥ 0,
    { exact sq_nonneg x },
    have ysqgte0 : y^2 ≥ 0,
    { exact sq_nonneg y },
    have xsqzero : x^2 = 0,
    { linarith },
    have ysqzero : y^2 = 0, by linarith,
    have xzero : x = 0, by exact pow_eq_zero xsqzero,
    have yzero : y = 0, by exact pow_eq_zero ysqzero,
    exact ⟨xzero, yzero⟩,
  },
  { show x = 0 ∧ y = 0 → x ^ 2 + y ^ 2 = 0,
    rintros ⟨xzero, yzero⟩,
    have xsqzero : x^2 = 0, {
      exact sq_eq_zero_iff.mpr xzero,
    },
    have ysqzero : y^2 = 0, {
      exact sq_eq_zero_iff.mpr yzero,
    },
    linarith,
  },
end

section

example (x y : ℝ) : abs (x + 3) < 5 → -8 < x ∧ x < 2 :=
begin
  rw abs_lt,
  intro h,
  split; linarith
end

example : 3 ∣ nat.gcd 6 15 :=
begin
  rw nat.dvd_gcd_iff,
  split; norm_num
end

end

theorem not_monotone_iff {f : ℝ → ℝ}:
  ¬ monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y :=
by { rw monotone, push_neg }

example : ¬ monotone (λ x : ℝ, -x) := begin
  rintros monomx,
  rw monotone at monomx,
  contrapose! monomx,
  use [0, 1],
  norm_num,
end

section
variables {α : Type*} [partial_order α]
variables a b : α

example : a < b ↔ a ≤ b ∧ a ≠ b :=
begin
  rw lt_iff_le_not_le,
  split,
  { show a ≤ b ∧ ¬b ≤ a → a ≤ b ∧ a ≠ b,
    rintros ⟨ aleb, nblea ⟩ ,
    split,
    { show a ≤ b, exact aleb, },
    { show a ≠ b,
      contrapose! nblea,
      exact eq.ge nblea,
    }
  },
  { show a ≤ b ∧ a ≠ b → a ≤ b ∧ ¬b ≤ a,
    rintros ⟨ aleb, aneqb ⟩, 
    split,
    { show a ≤ b, exact aleb,  },
    { show ¬b ≤ a,
      contrapose! aneqb,
      -- antisym을 써도 되나? preorder, partial order 헷갈리네
      -- partial order: refl, trans, antisymm
      -- preorder : reflexive, transitive
      exact ge_antisymm aneqb aleb,
    },
  },
end

end

section
variables {α : Type*} [preorder α]
variables a b c : α

-- only use le_refl, le_antisymm
-- . You do not need anything more than le_refl and le_trans.
example : ¬ a < a :=
begin
  rw lt_iff_le_not_le,
  by_contradiction h,
  have alea : a ≤ a, exact h.left,
  have nalea : ¬a ≤ a, exact h.right,
  exact nalea alea,
end

example (p q : Prop) (h : p → q ) : ¬q → ¬p  := begin
exact mt h,
end

example (p q r : Prop) (h : p → q → r) : (¬(q → r)) → ¬ p     := begin
exact mt h,
end

example (p q r : Prop) (h : p → q → r) : (¬r → ¬q) → ¬ p     := begin
sorry,
-- library_search,
end

-- class preorder (α : Type u) extends has_le α, has_lt α :=
-- (le_refl : ∀ a : α, a ≤ a)
-- (le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)
-- (lt := λ a b, a ≤ b ∧ ¬ b ≤ a)
-- (lt_iff_le_not_le : ∀ a b : α, a < b ↔ (a ≤ b ∧ ¬ b ≤ a) . order_laws_tac)
example : a < b → b < c → a < c :=
begin
  simp only [lt_iff_le_not_le],
  rintros abba bccb,
  have alec : a ≤ c, apply le_trans abba.left bccb.left,
  split,
  { show  a ≤ c, exact alec, },
  -- 다른 사람들은 어떻게 풀었나!
  { show ¬c ≤ a,
    by_contradiction,
    have cleb : c ≤ b, begin
     apply le_trans h abba.left,
    end,
    exact bccb.right cleb,
  },
end

end

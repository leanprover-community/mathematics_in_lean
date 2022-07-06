import data.nat.basic
import data.nat.parity
import tactic

open nat
/- These are pieces of data. -/

#check 2 + 2

def f (x : ℕ) := x + 3

#check f

/- These are propositions, of type `Prop`. -/

#check 2 + 2 = 4

def fermat_last_theorem :=
  ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x^n + y^n ≠ z^n

#check fermat_last_theorem

/- These are proofs of propositions. -/

theorem easy : 2 + 2 = 4 := rfl

#check easy

theorem hard : fermat_last_theorem := sorry

#check hard

/- Here are some proofs. -/

example : ∀ m n : nat, even n → even (m * n) :=
assume m n ⟨k, (hk : n = k + k)⟩,
have hmn : m * n = m * k + m * k,
  by rw [hk, mul_add],
show ∃ l, m * n = l + l,
  from ⟨_, hmn⟩

example : ∀ m n : nat, even n → even (m * n) :=
λ m n ⟨k, hk⟩, ⟨m * k, by rw [hk, mul_add]⟩

example : ∀ m n : nat, even n → even (m * n) :=
begin
  -- say m and n are natural numbers, and assume n=2*k
  rintros m n ⟨k, hk⟩,
  -- We need to prove m*n is twice a natural. Let's show it's twice m*k.
  use m * k,
  -- substitute in for n
  rw hk,
  -- and now it's obvious
  ring
end

example : ∀ m n : nat, even n → even (m * n) :=
by { rintros m n ⟨k, hk⟩, use m * k, rw hk, ring }

example : ∀ m n : nat, even n → even (m * n) :=
by intros; simp * with parity_simps


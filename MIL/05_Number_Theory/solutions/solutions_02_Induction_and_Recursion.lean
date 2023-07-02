import data.nat.prime
import algebra.big_operators
import tactic

def fac : ℕ → ℕ
| 0       := 1
| (n + 1) := (n + 1) * fac n

theorem pow_two_le_fac (n : ℕ) : 2^(n-1) ≤ fac n :=
begin
  cases n with n,
  { simp [fac] },
  induction n with n ih,
  { simp [fac] },
  simp at *,
  rw [pow_succ, fac],
  apply nat.mul_le_mul _ ih,
  repeat { apply nat.succ_le_succ },
  apply zero_le
end

section

variables {α : Type*} (s : finset ℕ) (f : ℕ → ℕ) (n : ℕ)

open_locale big_operators
open finset

theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i^2 = n * (n + 1) * (2 *n + 1) / 6 :=
begin
  symmetry, apply nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6),
  induction n with n ih,
  { simp },
  rw [finset.sum_range_succ, mul_add 6, ←ih, nat.succ_eq_add_one],
  ring
end

end

inductive my_nat
| zero : my_nat
| succ : my_nat → my_nat

namespace my_nat

def add : my_nat → my_nat → my_nat
| x zero     := x
| x (succ y) := succ (add x y)

def mul : my_nat → my_nat → my_nat
| x zero     := zero
| x (succ y) := add (mul x y) x

theorem zero_add (n : my_nat) : add zero n = n :=
begin
  induction n with n ih,
  { refl },
  rw [add, ih]
end

theorem succ_add (m n : my_nat) : add (succ m) n = succ (add m n) :=
begin
  induction n with n ih,
  { refl },
  rw [add, ih],
  refl
end

theorem add_comm (m n : my_nat) : add m n = add n m :=
begin
  induction n with n ih,
  { rw zero_add, refl },
  rw [add, succ_add, ih]
end

theorem add_assoc (m n k : my_nat) : add (add m n) k = add m (add n k) :=
begin
  induction k with k ih,
  { refl },
  rw [add, ih],
  refl
end

theorem mul_add  (m n k : my_nat) : mul m (add n k) = add (mul m n) (mul m k) :=
begin
  induction k with k ih,
  { refl },
  rw [add, mul, mul, ih, add_assoc]
end

theorem zero_mul (n : my_nat) : mul zero n = zero :=
begin
  induction n with n ih,
  { refl },
  rw [mul, ih],
  refl
end

theorem succ_mul (m n : my_nat) : mul (succ m) n = add (mul m n) n :=
begin
  induction n with n ih,
  { refl },
  rw [mul, mul, ih, add_assoc, add_assoc, add_comm n, succ_add],
  refl
end

theorem mul_comm (m n : my_nat) : mul m n = mul n m :=
begin
  induction n with n ih,
  { rw [zero_mul], refl },
  rw [mul, ih, succ_mul]
end

end my_nat

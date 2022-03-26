import algebra.big_operators.ring
import data.real.basic

@[ext] structure point := (x : ℝ) (y : ℝ) (z : ℝ)

namespace point

def add (a b : point) : point := ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

protected theorem add_assoc (a b c : point) :
  (a.add b).add c = a.add (b.add c) :=
by { simp [add, add_assoc] }

def smul (r : ℝ) (a : point) : point :=
⟨r * a.x, r * a.y, r * a.z⟩

theorem smul_distrib (r : ℝ) (a b : point) :
  (smul r a).add (smul r b) = smul r (a.add b) :=
by { simp [add, smul, mul_add] }

end point

structure standard_two_simplex :=
(x : ℝ)
(y : ℝ)
(z : ℝ)
(x_nonneg : 0 ≤ x)
(y_nonneg : 0 ≤ y)
(z_nonneg : 0 ≤ z)
(sum_eq   : x + y + z = 1)

namespace standard_two_simplex

noncomputable theory

def weighted_average (lambda : real)
    (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : standard_two_simplex) :
  standard_two_simplex :=
{ x        := lambda * a.x + (1 - lambda) * b.x,
  y        := lambda * a.y + (1 - lambda) * b.y,
  z        := lambda * a.z + (1 - lambda) * b.z,
  x_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.x_nonneg)
                (mul_nonneg (by linarith) b.x_nonneg),
  y_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.y_nonneg)
                (mul_nonneg (by linarith) b.y_nonneg),
  z_nonneg := add_nonneg (mul_nonneg lambda_nonneg a.z_nonneg)
                (mul_nonneg (by linarith) b.z_nonneg),
  sum_eq   :=
    begin
      transitivity (a.x + a.y + a.z) * lambda + (b.x + b.y + b.z) * (1 - lambda),
      { ring },
      simp [a.sum_eq, b.sum_eq]
    end }

end standard_two_simplex

open_locale big_operators

structure standard_simplex (n : ℕ) :=
(v          : fin n → ℝ)
(nonneg     : ∀ i : fin n, 0 ≤ v i)
(sum_eq_one : ∑ i, v i = 1)

namespace standard_simplex

def midpoint (n : ℕ) (a b : standard_simplex n) : standard_simplex n :=
{ v := λ i, (a.v i + b.v i) / 2,
  nonneg :=
    begin
      intro i,
      apply div_nonneg,
      { linarith [a.nonneg i, b.nonneg i] },
      norm_num
    end,
  sum_eq_one :=
    begin
      simp [div_eq_mul_inv, ←finset.sum_mul, finset.sum_add_distrib,
        a.sum_eq_one, b.sum_eq_one],
      field_simp
    end  }

end standard_simplex

namespace standard_simplex

def weighted_average {n : ℕ} (lambda : real)
    (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
    (a b : standard_simplex n) : standard_simplex n :=
{ v          := λ i, lambda * a.v i + (1 - lambda) * b.v i,
  nonneg     := λ i, add_nonneg (mul_nonneg lambda_nonneg (a.nonneg i))
                  (mul_nonneg (by linarith) (b.nonneg i)),
  sum_eq_one :=
    begin
      transitivity lambda * (∑ i, a.v i) + (1 - lambda) * (∑ i, b.v i),
      { rw [finset.sum_add_distrib, finset.mul_sum, finset.mul_sum] },
      simp [a.sum_eq_one, b.sum_eq_one]
    end }

end standard_simplex


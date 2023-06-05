import data.nat.gcd
import data.real.irrational

lemma even_of_even_sqr {m : ℕ} (h : 2 ∣ m^2) : 2 ∣ m :=
begin
  rw [pow_two, nat.prime_two.dvd_mul] at h,
  cases h; assumption
end

example {m n : ℕ} (coprime_mn : m.coprime n) : m^2 ≠ 2 * n^2 :=
begin
  intro sqr_eq,
  have : 2 ∣ m,
  { apply even_of_even_sqr,
    rw sqr_eq,
    apply dvd_mul_right },
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this,
  have : 2 * (2 * k^2) = 2 * n^2,
  { rw [←sqr_eq, meq], ring },
  have : 2 * k^2 = n^2,
    from (mul_right_inj' (by norm_num)).mp this,
  have : 2 ∣ n,
  { apply even_of_even_sqr,
    rw ←this,
    apply dvd_mul_right },
  have : 2 ∣ m.gcd n,
    by apply nat.dvd_gcd; assumption,
  have : 2 ∣ 1,
  { convert this, symmetry, exact coprime_mn },
  norm_num at this
end

example {m n p : ℕ} (coprime_mn : m.coprime n) (prime_p : p.prime) : m^2 ≠ p * n^2 :=
begin
  intro sqr_eq,
  have : p ∣ m,
  { apply prime_p.dvd_of_dvd_pow,
    rw sqr_eq,
    apply dvd_mul_right },
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this,
  have : p * (p * k^2) = p * n^2,
  { rw [←sqr_eq, meq], ring },
  have : p * k^2 = n^2,
  { apply (mul_right_inj' _).mp this,
    exact prime_p.ne_zero },
  have : p ∣ n,
  { apply prime_p.dvd_of_dvd_pow,
    rw ←this,
    apply dvd_mul_right },
  have : p ∣ nat.gcd m n,
  { apply nat.dvd_gcd; assumption },
  have : p ∣ 1,
  { convert this, symmetry, exact coprime_mn },
  have : 2 ≤ 1,
  { apply prime_p.two_le.trans,
    exact nat.le_of_dvd zero_lt_one this },
  norm_num at this
end


theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
  (m * n).factorization p = m.factorization p + n.factorization p :=
by { rw nat.factorization_mul mnez nnez, refl }

theorem factorization_pow' (n k p : ℕ) :
  (n^k).factorization p = k * n.factorization p :=
by { rw nat.factorization_pow, refl }

theorem nat.prime.factorization' {p : ℕ} (prime_p : p.prime) :
  p.factorization p = 1 :=
by { rw prime_p.factorization, simp }


example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.prime) : m^2 ≠ p * n^2 :=
begin
  intro sqr_eq,
  have nsqr_nez : n^2 ≠ 0,
    by simpa,
  have eq1 : nat.factorization (m^2) p = 2 * m.factorization p,
    by { rw factorization_pow' },
  have eq2 : (p * n^2).factorization p = 2 * n.factorization p + 1,
  { rw [factorization_mul' prime_p.ne_zero nsqr_nez, prime_p.factorization',
        factorization_pow', add_comm] },
  have : (2 * m.factorization p) % 2 = (2 * n.factorization p + 1) % 2,
  { rw [←eq1, sqr_eq, eq2] },
  rw [add_comm, nat.add_mul_mod_self_left, nat.mul_mod_right] at this,
  norm_num at this
end

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m^k = r * n^k)
  {p : ℕ} (prime_p : p.prime) : k ∣ r.factorization p :=
begin
  cases r with r,
  { simp },
  have npow_nz : n^k ≠ 0 := λ npowz, nnz (pow_eq_zero npowz),
  have eq1 : (m^k).factorization p = k * m.factorization p,
    by rw factorization_pow',
  have eq2 : (r.succ * n^k).factorization p =
      k * n.factorization p + r.succ.factorization p,
  { rw [factorization_mul' r.succ_ne_zero npow_nz, factorization_pow',
         add_comm] },
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p,
  { rw [←eq1, pow_eq, eq2, add_comm, nat.add_sub_cancel] },
  rw this,
  apply nat.dvd_sub'; apply nat.dvd_mul_right
end


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

example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.prime) : m^2 ≠ p * n^2 :=
begin
  intro sqr_eq,
  have nsqr_nez : n^2 ≠ 0,
    by simpa,
  have eq1 : (m^2).factors.count p = 2 * m.factors.count p,
    by rw nat.factors_count_pow,
  have eq2 : (p * n^2).factors.count p = 2 * n.factors.count p + 1,
  { rw [nat.count_factors_mul_of_pos prime_p.pos (nat.pos_of_ne_zero nsqr_nez),
      nat.factors_prime prime_p, nat.factors_count_pow],
    simp [add_comm] },
  have : (2 * m.factors.count p) % 2 = (2 * n.factors.count p + 1) % 2,
  { rw [←eq1, sqr_eq, eq2] },
  rw [add_comm, nat.add_mul_mod_self_left, nat.mul_mod_right] at this,
  norm_num at this
end

example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m^k = r * n^k) :
  ∀ p : ℕ, p.prime → k ∣ r.factors.count p :=
begin
  intros p prime_p,
  cases r with r,
  { simp },
  have npow_nz : n^k ≠ 0 := λ npowz, nnz (pow_eq_zero npowz),
  have eq1 : (m^k).factors.count p = k * m.factors.count p,
    by rw nat.factors_count_pow,
  have eq2 : (r.succ * n^k).factors.count p =
      k * n.factors.count p + r.succ.factors.count p,
  { rw [nat.count_factors_mul_of_pos (r.succ_pos) (nat.pos_of_ne_zero npow_nz),
      nat.factors_count_pow],
    simp [add_comm] },
  have : r.succ.factors.count p = k * m.factors.count p - k * n.factors.count p,
  { rw [←eq1, pow_eq, eq2, add_comm, nat.add_sub_cancel] },
  rw this,
  apply nat.dvd_sub'; apply nat.dvd_mul_right
end


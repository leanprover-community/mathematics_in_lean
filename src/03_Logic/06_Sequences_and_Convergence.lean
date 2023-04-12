import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

example : (λ x y : ℝ, (x + y)^2) = (λ x y : ℝ, x^2 + 2*x*y + y^2) :=
by { ext, ring }

example (a b : ℝ) : abs a = abs (a - b + b) :=
by  { congr, ring }

example {a : ℝ} (h : 1 < a) : a < a * a :=
begin
  convert (mul_lt_mul_right _).2 h,
  { rw [one_mul] },
  exact lt_trans zero_lt_one h
end

theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
begin
  intros ε εpos,
  use 0,
  intros n nge, dsimp,
  rw [sub_self, abs_zero],
  apply εpos
end

-- 이것보다 잘 할 수 있을 거 같은데
theorem converges_to_add {s t : ℕ → ℝ} {a b : ℝ}
  (cs : converges_to s a) (ct : converges_to t b):
converges_to (λ n, s n + t n) (a + b) :=
begin
  intros ε εpos, dsimp,
  have ε2pos : 0 < ε / 2,
  { linarith },
  cases cs (ε / 2) ε2pos with Ns hs,
  cases ct (ε / 2) ε2pos with Nt ht,
  use max Ns Nt,
  intros bigger_n max_N_le_n,
  -- use n for `hs: ∀ (n : ℕ), n ≥ Ns → |s n - a| < ε / 2`,
  have hs' : abs (s bigger_n - a) < ε / 2,
  { apply hs, exact le_of_max_le_left max_N_le_n, },
  have ht' : abs (t bigger_n - b) < ε / 2,
  { apply ht, exact le_of_max_le_right max_N_le_n, },
  have eta_eq_two_eta_div_two : ε = (ε / 2) + (ε / 2), by ring,
  have hs'_plus_ht' : abs (s bigger_n - a) + abs (t bigger_n - b) < ε,
  { rw eta_eq_two_eta_div_two, linarith },
  have triangle_ineq : abs (s bigger_n + t bigger_n - (a + b)) ≤ abs (s bigger_n - a) + abs (t bigger_n - b),
  { have k: s bigger_n + t bigger_n - (a + b) = (s bigger_n - a) + (t bigger_n - b), { ring },
    rw k,
    exact abs_add _ _ },
  linarith,
end

-- def converges_to (s : ℕ → ℝ) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε
theorem converges_to_mul_const {s : ℕ → ℝ} {a : ℝ}
    (c : ℝ) (cs : converges_to s a) :
  converges_to (λ n, c * s n) (c * a) :=
begin
  by_cases h : c = 0,
  { convert converges_to_const 0,
    { ext, rw [h, zero_mul] },
    rw [h, zero_mul] },
  have acpos : 0 < abs c,
    from abs_pos.mpr h,

  intros ε ε_pos, dsimp,
  cases cs (ε / abs c) (div_pos ε_pos acpos) with N h,
  use N,
  intros n n_gte_N,
  have h2: |s n - a| < ε / |c|, {
    apply h, linarith,
  },
  have h3: |c| * |s n - a| < ε, {
    rw mul_comm,
    apply (lt_div_iff acpos).mp,
    linarith,
  },
  have h4: |c| * |s n - a| = |c * s n - c * a|, {
    rw ← abs_mul c _,
    ring_nf,
  },
  linarith,
end

-- def converges_to (s : ℕ → ℝ) (a : ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε
theorem exists_abs_le_of_converges_to {s : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) :
  ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
begin
  cases cs 1 zero_lt_one with N h,
  use [N, abs a + 1],
  intros n n_ge_N,
  show |s n| < |a| + 1,
  have h1: |s n - a| < 1, begin
    apply h, linarith,
  end,
  have h2: |s n - a| + |a| < |a| + 1, begin
    linarith,
  end,
  have h3: |s n| ≤ |s n - a| + |a|, {
    have h3_1: |s n - a + a| ≤ |s n - a| + |a|, {
      apply abs_add,
    },
    have h3_2: |s n - a + a| = |s n|, {
      ring_nf,
    },
    rw ← h3_2,
    exact h3_1,
  },
  linarith,
end

-- 이건 좀 아닌데...
lemma aux {s t : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) (ct : converges_to t 0) :
  converges_to (λ n, s n * t n) 0 :=
begin
  intros ε εpos, dsimp,
  rcases exists_abs_le_of_converges_to cs with ⟨N₀, B, h₀⟩,
  have Bpos : 0 < B,
    from lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _)),
  have pos₀ : ε / B > 0,
    from div_pos εpos Bpos,
  cases ct _ pos₀ with N₁ h₁,
  let max_N := max N₀ N₁,
  use max_N,
  intros n n_ge_max_N,

  have k1: |t n - 0| < ε / B, begin
    apply h₁, exact le_of_max_le_right n_ge_max_N,
  end,
  have k1_1: |t n| < ε / B, begin
    have k1_1_1: |t n - 0| = |t n|, {
      ring_nf,
    },
    rw k1_1_1 at k1,
    exact k1,
  end,
  have k2: |s n| < B, begin
    apply h₀, exact le_of_max_le_left n_ge_max_N,
  end,
  -- have k3: |s n | * | t n| < B * (ε / B) , begin
  have k3: |s n | * | t n| < ε, begin
    -- cases |t n | = 0 or not
    cases classical.em (|t n| = 0) with tn_0 tn_nonzero,
    { rw tn_0, ring_nf, linarith, },
    have k3_1: |s n | * | t n| < B * |t n|, {
      apply mul_lt_mul_of_pos_right k2 ,
      rcases lt_trichotomy 0 (|t n|) with tn_pos | tn_zero | tn_neg,
      { exact tn_pos },
      { rw tn_zero at tn_nonzero, contradiction },
      { have tn_nonneg: 0 ≤ |t n|, {
          apply abs_nonneg,
        },
        linarith,
      },
    },
    have k3_2: B * |t n| < B * (ε / B), {
      apply mul_lt_mul_of_pos_left k1_1,
      exact Bpos,
    },
    have k3_e: B * (ε / B ) = ε , {
      rw  ← mul_div_assoc,
      rw mul_comm,
      rw mul_div_assoc, rw div_self,
      ring, linarith,
    },
    linarith,
  end,
  have k4: |s n * t n - 0| = |s n |* |t n|, {
    ring_nf,
    exact abs_mul (t n) (s n),
  },
  rw k4,
  exact k3,
end

theorem converges_to_mul {s t : ℕ → ℝ} {a b : ℝ}
    (cs : converges_to s a) (ct : converges_to t b):
  converges_to (λ n, s n * t n) (a * b) :=
begin
  have h₁ : converges_to (λ n, s n * (t n - b)) 0,
  { apply aux cs,
    convert converges_to_add ct (converges_to_const (-b)),
    ring },
  convert (converges_to_add h₁ (converges_to_mul_const b cs)),
  { ext, ring },
  ring
end

theorem converges_to_unique {s : ℕ → ℝ} {a b : ℝ}
    (sa : converges_to s a) (sb : converges_to s b) :
  a = b :=
begin
  by_contradiction abne,
  have : abs (a - b) > 0,
  { apply abs_pos.mpr,
    by_contradiction aeqb,
    have k1: a = b, { linarith, },
    contradiction,
    exact has_add.to_covariant_class_left ℝ,
  },
  let ε := abs (a - b) / 2,
  have εpos : ε > 0,
  { change abs (a - b) / 2 > 0, linarith },
  cases sa ε εpos with Na hNa,
  cases sb ε εpos with Nb hNb,
  let N := max Na Nb,
  have absa : abs (s N - a) < ε,
  { apply hNa, exact le_max_left Na Nb, },
  have absb : abs (s N - b) < ε,
  { apply hNb, exact le_max_right Na Nb, },

  have k1: s N - a < ε, { exact lt_of_abs_lt absa, },
  have k2: - ε < s N - a, { exact neg_lt_of_abs_lt absa, },
  have k3: s N - b < ε , { exact lt_of_abs_lt absb, },
  have k4: - ε < s N - b, { exact neg_lt_of_abs_lt absb, },
  have k5: - ε - ε < s N - b - (s N - a), { exact sub_lt_sub k4 k1, },
  have k6: s N - b - (s N - a) < ε - (-ε) , { exact sub_lt_sub k3 k2,},
  have k7: -| a - b | < a - b, {
    have : | a - b | = (|a - b| / 2) + (| a - b | / 2), ring_nf,
    have : | a - b | = ε + ε , { rw this, },
    have : -ε -ε = - | a - b|, { linarith, },
    have : a - b = s N - b - (s N - a), { ring_nf,}, 
    linarith,
  },
  have k8: a - b < | a - b |, {
    have : | a - b | = (|a - b| / 2) + (| a - b | / 2), ring_nf,
    have : | a - b | = ε + ε , { rw this, },
    have : | a - b | = ε - (-ε ), {linarith,},
    have : a - b = s N - b - (s N - a), { ring_nf, },
    linarith,
  },
  rcases lt_trichotomy (a - b) 0 with abm | abz | abp,
  { have : |a - b| = - (a - b), exact abs_of_neg abm,
  linarith, },
  { have aeqb : a = b, exact sub_eq_zero.mp abz, apply abne aeqb,},
  { have : | a - b | = a - b, exact abs_of_pos abp, linarith,},
 
end

section
variables {α : Type*} [linear_order α]

def converges_to' (s : α → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

end


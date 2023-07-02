import data.real.basic

def converges_to (s : ℕ → ℝ) (a : ℝ) :=
∀ ε > 0, ∃ N, ∀ n ≥ N, abs (s n - a) < ε

theorem converges_to_const (a : ℝ) : converges_to (λ x : ℕ, a) a :=
begin
  intros ε εpos,
  use 0,
  intros n nge, dsimp,
  rw [sub_self, abs_zero],
  apply εpos
end

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
  intros n hn,
  have ngeNs : n ≥ Ns := le_of_max_le_left hn,
  have ngeNt : n ≥ Nt := le_of_max_le_right hn,
  calc
    |s n + t n - (a + b)| = | s n - a + (t n - b) | :
      by { congr, ring }
    ... ≤  | s n - a | + | (t n - b) | :
      abs_add _ _
    ... < ε / 2 + ε / 2 : add_lt_add (hs n ngeNs) (ht n ngeNt)
    ... = ε : by norm_num
end

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
  intros ε εpos, dsimp,
  have εcpos : 0 < ε / abs c,
  { apply div_pos εpos acpos },
  cases cs (ε / abs c) εcpos with Ns hs,
  use Ns,
  intros n ngt,
  calc
    |c * s n - c * a| = |c| * |s n - a| :
      by { rw [←abs_mul, mul_sub] }
    ... < |c| * (ε / |c|) :
      mul_lt_mul_of_pos_left (hs n ngt) acpos
    ... = ε : mul_div_cancel' _ (ne_of_lt acpos).symm
end

theorem exists_abs_le_of_converges_to {s : ℕ → ℝ} {a : ℝ}
    (cs : converges_to s a) :
  ∃ N b, ∀ n, N ≤ n → abs (s n) < b :=
begin
  cases cs 1 zero_lt_one with N h,
  use [N, abs a + 1],
  intros n ngt,
  calc
    |s n| = |s n - a + a| : by { congr, abel }
    ... ≤ |s n - a| + |a| : abs_add _ _
    ... < |a| + 1 : by linarith [h n ngt]
end

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
  use max N₀ N₁,
  intros n ngt,
  have ngeN₀ : n ≥ N₀ := le_of_max_le_left ngt,
  have ngeN₁ : n ≥ N₁ := le_of_max_le_right ngt,
  calc
    |s n * t n - 0| = |s n| * |t n - 0| :
      by rw [sub_zero, abs_mul, sub_zero]
    ... < B * (ε / B) :
      mul_lt_mul'' (h₀ n ngeN₀) (h₁ n ngeN₁) (abs_nonneg _) (abs_nonneg _)
    ... = ε : mul_div_cancel' _ (ne_of_lt Bpos).symm
end

theorem converges_to_muL {s t : ℕ → ℝ} {a b : ℝ}
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
  { apply lt_of_le_of_ne,
    { apply abs_nonneg },
      intro h'',
      apply abne,
      apply eq_of_abs_sub_eq_zero h''.symm, },
  let ε := abs (a - b) / 2,
  have εpos : ε > 0,
  { change abs (a - b) / 2 > 0, linarith },
  cases sa ε εpos with Na hNa,
  cases sb ε εpos with Nb hNb,
  let N := max Na Nb,
  have absa : abs (s N - a) < ε,
  { apply hNa, apply le_max_left },
  have absb : abs (s N - b) < ε,
  { apply hNb, apply le_max_right },
  have : abs (a - b) < abs (a - b),
    calc
      abs (a - b) = abs (- (s N - a) + (s N - b)) :
        by { congr, ring }
      ... ≤ abs (- (s N - a)) + abs (s N - b) :
        abs_add _ _
      ... = abs (s N - a) + abs (s N - b) :
        by rw [abs_neg]
      ... < ε + ε : add_lt_add absa absb
      ... = abs (a - b) : by norm_num,
  exact lt_irrefl _ this
end


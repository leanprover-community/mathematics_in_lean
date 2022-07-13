import topology.instances.real
import analysis.normed_space.banach_steinhaus

open set filter
open_locale topological_space filter

example {f : ℝ → X} (hf : continuous f) : continuous (λ x : ℝ, f (x^2 + x)) :=
hf.comp $ (continuous_pow 2).add continuous_id


example {u : ℕ → X} (hu : tendsto u at_top (𝓝 a)) {s : set X} (hs : ∀ n, u n ∈ s) : 
  a ∈ closure s :=
begin
  rw metric.tendsto_at_top at hu,
  rw metric.mem_closure_iff,
  intros ε ε_pos,
  rcases hu ε ε_pos with ⟨N, hN⟩,
  refine ⟨u N, hs _, _⟩,
  rw dist_comm,
  exact hN N le_rfl
end


example {u : ℕ → X} (hu : ∀ (n : ℕ), dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) :
  cauchy_seq u :=
begin
  rw metric.cauchy_seq_iff',  
  intros ε ε_pos,
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε,
  { have : tendsto (λ N : ℕ, (1 / 2 ^ N * 2 : ℝ)) at_top (𝓝 0),
    { rw ← zero_mul (2 : ℝ),
      apply tendsto.mul,
      simp_rw ← one_div_pow (2 : ℝ),
      apply tendsto_pow_at_top_nhds_0_of_lt_1 ; linarith,
      exact tendsto_const_nhds },
    rcases (at_top_basis.tendsto_iff (nhds_basis_Ioo_pos (0 : ℝ))).mp this ε ε_pos with ⟨N, H, hN⟩,
    exact  ⟨N, by simpa using (hN N le_rfl).2⟩ },
  use N,
  intros n hn,
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn,
  calc dist (u (N + k)) (u N) = dist (u (N+0)) (u (N + k)) : by rw [dist_comm, add_zero]
  ... ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) : dist_le_range_sum_dist (λ i, u (N+i)) k
  ... ≤ ∑ i in range k, (1/2 : ℝ) ^ (N+i) : sum_le_sum (λ i hi, hu $ N+i)
  ... = 1/2^N*∑ i in range k, (1 / 2)^i : by simp_rw [← one_div_pow, pow_add, ← mul_sum]
  ... ≤ 1/2^N*2 : mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (one_div_nonneg.mpr (pow_nonneg (zero_le_two : (0 : ℝ) ≤ 2)_))
  ... < ε : hN
end

example [complete_space X] (f : ℕ → set X) (ho : ∀ n, is_open (f n)) (hd : ∀ n, dense (f n)) : dense (⋂n, f n) :=
begin
  let B : ℕ → ℝ := λ n, (1/2)^n,
  have Bpos : ∀ n, 0 < B n, from λ n, (pow_pos sorry n),
  /- Translate the density assumption into two functions `center` and `radius` associating
  to any n, x, δ, δpos a center and a positive radius such that
  `closed_ball center radius` is included both in `f n` and in `closed_ball x δ`.
  We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have : ∀ (n : ℕ)  (x : X) (δ > 0), ∃ (y : X) (r > 0), r ≤ B (n+1) ∧ closed_ball y r ⊆ (closed_ball x δ) ∩ f n,
  { intros n x δ δpos,
    have : x ∈ closure (f n) := hd n x,
    rcases metric.mem_closure_iff.1 this (δ/2) (half_pos δpos) with ⟨y, ys, xy⟩,
    rw dist_comm at xy,
    obtain ⟨r, rpos, hr⟩ : ∃ r > 0, closed_ball y r ⊆ f n :=
      nhds_basis_closed_ball.mem_iff.1 (is_open_iff_mem_nhds.1 (ho n) y ys),
    refine ⟨y, min (min (δ/2) r) (B (n+1)), _, _, λz hz, ⟨_, _⟩⟩,
    show 0 < min (min (δ / 2) r) (B (n+1)),
      from lt_min (lt_min (half_pos δpos) rpos) (Bpos (n+1)),
    show min (min (δ / 2) r) (B (n+1)) ≤ B (n+1), from min_le_right _ _,
    show z ∈ closed_ball x δ, from calc
      dist z x ≤ dist z y + dist y x : dist_triangle _ _ _
      ... ≤ (min (min (δ / 2) r) (B (n+1))) + (δ/2) : add_le_add hz xy.le
      ... ≤ δ/2 + δ/2 : add_le_add_right ((min_le_left _ _).trans (min_le_left _ _)) _ 
      ... = δ : add_halves δ,
    show z ∈ f n, from hr (calc
      dist z y ≤ min (min (δ / 2) r) (B (n+1)) : hz
      ... ≤ r : (min_le_left _ _).trans (min_le_right _ _)) },
  choose! center radius Hpos HB Hball using this,
  refine λ x, (mem_closure_iff_nhds_basis nhds_basis_closed_ball).2 (λ ε εpos, _),
  /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x` belonging to all
  `f n`. For this, we construct inductively a sequence `F n = (c n, r n)` such that the closed ball
  `closed_ball (c n) (r n)` is included in the previous ball and in `f n`, and such that
  `r n` is small enough to ensure that `c n` is a Cauchy sequence. Then `c n` converges to a
  limit which belongs to all the `f n`. -/
  let F : ℕ → (X × ℝ) := λn, nat.rec_on n (prod.mk x (min ε (B 0)))
                              (λn p, prod.mk (center n p.1 p.2) (radius n p.1 p.2)),
  let c : ℕ → X := λ n, (F n).1,
  let r : ℕ → ℝ := λ n, (F n).2,
  have rpos : ∀ n, 0 < r n,
  { assume n,
    induction n with n hn,
    exact lt_min εpos (Bpos 0),
    exact Hpos n (c n) (r n) hn },
  
  have rB : ∀n, r n ≤ B n,
  { assume n,
    induction n with n hn,
    exact min_le_right _ _,
    exact HB n (c n) (r n) (rpos n) },
  have incl : ∀n, closed_ball (c (n+1)) (r (n+1)) ⊆ (closed_ball (c n) (r n)) ∩ (f n) :=
    λ n, Hball n (c n) (r n) (rpos n),
  have cdist : ∀ n, dist (c n) (c (n+1)) ≤ B n,
  { assume n,
    rw dist_comm,
    have A : c (n+1) ∈ closed_ball (c (n+1)) (r (n+1)) := mem_closed_ball_self (rpos $ n +1).le,
    have I := calc
      closed_ball (c (n+1)) (r (n+1)) ⊆ closed_ball (c n) (r n) :
         (incl n).trans (inter_subset_left _ _)
      ... ⊆ closed_ball (c n) (B n) : closed_ball_subset_closed_ball (rB n),
    exact I A },
  have : cauchy_seq c,
  from cauchy_seq_of_le_geometric_two' cdist,
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchy_seq_tendsto_of_complete this with ⟨y, ylim⟩,
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y,
  
  have I : ∀n, ∀ m ≥ n, closed_ball (c m) (r m) ⊆ closed_ball (c n) (r n),
  { assume n,
    refine nat.le_induction _ (λm hnm h, _),
    { exact subset.rfl },
    { exact (incl m).trans ((set.inter_subset_left _ _).trans h) }},
  have yball : ∀n, y ∈ closed_ball (c n) (r n),
  { assume n,
    refine is_closed_ball.mem_of_tendsto ylim _,
    refine (filter.eventually_ge_at_top n).mono (λ m hm, _),
    exact I n m hm (mem_closed_ball_self (rpos _).le) },
  split,
  { suffices : ∀ n, y ∈ f n, by rwa set.mem_Inter,    
    intro n,
    have : closed_ball (c (n+1)) (r (n+1)) ⊆ f n := subset.trans (incl n) (inter_subset_right _ _),
    exact this (yball (n+1)) },
  calc dist y x ≤ r 0 : yball 0
            ... ≤ ε : min_le_left _ _,
end


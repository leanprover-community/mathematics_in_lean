import topology.instances.real
import analysis.normed_space.banach_steinhaus

open set filter
open_locale topological_space filter


variables {X : Type*} [metric_space X] (a b c : X)

#check (dist a b : ℝ)

#check (dist_nonneg : 0 ≤ dist a b)

#check (dist_eq_zero : dist a b  = 0 ↔ a = b)

#check (dist_comm a b : dist a b  = dist b a)

#check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)


-- Note the next three lines are not quoted, their purpose is to make sure those things don't get renamed while we're looking elsewhere.
#check emetric_space
#check pseudo_metric_space
#check pseudo_emetric_space



example {u : ℕ → X} {a : X} : 
  tendsto u at_top (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
metric.tendsto_at_top

example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} :
  continuous f ↔
  ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
metric.continuous_iff



example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) : 
  continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
by continuity


example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) : 
  continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
continuous_dist.comp ((hf.comp continuous_fst).prod_mk (hf.comp continuous_snd))




example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) : 
  continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
begin
  apply continuous.dist,
  exact hf.comp continuous_fst,
  exact hf.comp continuous_snd
end

example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) : 
  continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
(hf.comp continuous_fst).dist (hf.comp continuous_snd)



example {X Y : Type*} [metric_space X] [metric_space Y] {f : X → Y} (hf : continuous f) : 
  continuous (λ p : X × X, dist (f p.1) (f p.2)) :=
hf.fst'.dist hf.snd'



example {f : ℝ → X} (hf : continuous f) : continuous (λ x : ℝ, f (x^2 + x)) :=
sorry


example {f : ℝ → X} (hf : continuous f) : continuous (λ x : ℝ, f (x^2 + x)) :=
hf.comp $ (continuous_pow 2).add continuous_id




example {X Y : Type*} [metric_space X] [metric_space Y] (f : X → Y) (a : X) : 
continuous_at f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
metric.continuous_at_iff



variables r : ℝ

example : metric.ball a r = {b | dist b a < r} := rfl

example : metric.closed_ball a r = {b | dist b a ≤ r} := rfl



example (hr : 0 < r) : a ∈ metric.ball a r := metric.mem_ball_self hr

example (hr : 0 ≤ r) : a ∈ metric.closed_ball a r := metric.mem_closed_ball_self hr


example (s : set X) : is_open s ↔ ∀ x ∈ s, ∃ ε > 0, metric.ball x ε ⊆ s :=
metric.is_open_iff



example {s : set X} : is_closed s ↔ is_open sᶜ :=
is_open_compl_iff.symm

example {s : set X} (hs : is_closed s) {u : ℕ → X} (hu : tendsto u at_top (𝓝 a)) 
  (hus : ∀ n, u n ∈ s) : a ∈ s :=
hs.mem_of_tendsto hu (eventually_of_forall hus)

example {s : set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ metric.ball b ε :=
metric.mem_closure_iff


example {u : ℕ → X} (hu : tendsto u at_top (𝓝 a)) {s : set X} (hs : ∀ n, u n ∈ s) : 
  a ∈ closure s :=
sorry


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



example {x : X} {s : set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, metric.ball x ε ⊆ s :=
metric.nhds_basis_ball.mem_iff

example {x : X} {s : set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, metric.closed_ball x ε ⊆ s :=
metric.nhds_basis_closed_ball.mem_iff




example : is_compact (set.Icc 0 1 : set ℝ) :=
is_compact_Icc

example {s : set X} (hs : is_compact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
  ∃ a ∈ s, ∃ φ : ℕ → ℕ, strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 a) :=
hs.tendsto_subseq hu

example {s : set X} (hs : is_compact s) (hs' : s.nonempty) 
  {f : X → ℝ} (hfs : continuous_on f s) :
  ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
hs.exists_forall_le hs' hfs

example {s : set X} (hs : is_compact s) (hs' : s.nonempty) 
  {f : X → ℝ} (hfs : continuous_on f s) :
  ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
hs.exists_forall_ge hs' hfs

example {s : set X} (hs : is_compact s) : is_closed s :=
hs.is_closed



example {X : Type*} [metric_space X] [compact_space X] : is_compact (univ : set X) :=
compact_univ


#check is_compact.is_closed


example {X : Type*} [metric_space X] {Y : Type*} [metric_space Y] {f : X → Y} : 
  uniform_continuous f ↔ ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
metric.uniform_continuous_iff



example {X : Type*} [metric_space X] [compact_space X] {Y : Type*} [metric_space Y]
  {f : X → Y} (hf : continuous f) : uniform_continuous f :=
sorry


example {X : Type*} [metric_space X] [compact_space X] {Y : Type*} [metric_space Y]
  {f : X → Y} (hf : continuous f) : uniform_continuous f :=
begin
  rw metric.uniform_continuous_iff,
  intros ε ε_pos,
  let φ : X × X → ℝ := λ p, dist (f p.1) (f p.2),
  have φ_cont : continuous φ := hf.fst'.dist hf.snd',
  let K := { p : X × X | ε ≤ φ p },
  have K_closed : is_closed K := is_closed_le continuous_const φ_cont,
  have K_cpct : is_compact K := K_closed.is_compact,
  cases eq_empty_or_nonempty K with hK hK,
  { use [1, by norm_num],
    intros x y hxy,
    have : (x, y) ∉ K, by simp [hK],
    simpa [K] },
  { rcases K_cpct.exists_forall_le hK continuous_dist.continuous_on with ⟨⟨x₀, x₁⟩, xx_in, H⟩,
    use dist x₀ x₁,
    split,
    { change _ < _,
      rw dist_pos,
      intro h,
      have : ε ≤ 0, by simpa [*] using xx_in,
      linarith },
    { intros x x',
      contrapose!,
      intros hxx',
      exact H (x, x') hxx' } },
end



example (u : ℕ → X) : cauchy_seq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N,  ∀ n ≥ N, dist (u m) (u n) < ε :=
metric.cauchy_seq_iff

example (u : ℕ → X) : cauchy_seq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
metric.cauchy_seq_iff'


example [complete_space X] (u : ℕ → X) (hu : cauchy_seq u) : ∃ x, tendsto u at_top (𝓝 x) :=
cauchy_seq_tendsto_of_complete hu



open_locale big_operators
open finset


lemma cauchy_seq_of_le_geometric_two' {u : ℕ → X} (hu : ∀ (n : ℕ), dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) :
  cauchy_seq u :=
begin
  rw metric.cauchy_seq_iff',  
  intros ε ε_pos,
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε,
  { sorry },
  use N,
  intros n hn,
  obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn,
  calc dist (u (N + k)) (u N) = dist (u (N+0)) (u (N + k)) : sorry
  ... ≤ ∑ i in range k, dist (u (N + i)) (u (N + (i + 1))) : sorry
  ... ≤ ∑ i in range k, (1/2 : ℝ)^(N+i) : sorry
  ... = 1/2^N*∑ i in range k, (1 / 2) ^ i : sorry
  ... ≤ 1/2^N*2 : sorry
  ... < ε : sorry
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


open metric

example [complete_space X] (f : ℕ → set X) (ho : ∀ n, is_open (f n)) (hd : ∀ n, dense (f n)) : dense (⋂n, f n) :=
begin
  let B : ℕ → ℝ := λ n, (1/2)^n,
  have Bpos : ∀ n, 0 < B n, sorry,
  /- Translate the density assumption into two functions `center` and `radius` associating
  to any n, x, δ, δpos a center and a positive radius such that
  `closed_ball center radius` is included both in `f n` and in `closed_ball x δ`.
  We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
  have : ∀ (n : ℕ)  (x : X) (δ > 0), ∃ (y : X) (r > 0), r ≤ B (n+1) ∧ closed_ball y r ⊆ (closed_ball x δ) ∩ f n,
  { sorry },
  choose! center radius Hpos HB Hball using this,
  intros x,
  rw mem_closure_iff_nhds_basis nhds_basis_closed_ball,
  intros ε εpos,
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
  { sorry },
  
  have rB : ∀n, r n ≤ B n,
  { sorry },
  have incl : ∀n, closed_ball (c (n+1)) (r (n+1)) ⊆ (closed_ball (c n) (r n)) ∩ (f n),
  { sorry },
  have cdist : ∀ n, dist (c n) (c (n+1)) ≤ B n,
  { sorry },
  have : cauchy_seq c, from cauchy_seq_of_le_geometric_two' cdist,
  -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
  rcases cauchy_seq_tendsto_of_complete this with ⟨y, ylim⟩,
  -- this point `y` will be the desired point. We will check that it belongs to all
  -- `f n` and to `ball x ε`.
  use y,
  have I : ∀n, ∀ m ≥ n, closed_ball (c m) (r m) ⊆ closed_ball (c n) (r n),
  { sorry },
  have yball : ∀n, y ∈ closed_ball (c n) (r n),
  { sorry },
  sorry
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



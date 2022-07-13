import topology.instances.real
import analysis.normed_space.banach_steinhaus

open set filter
open_locale topological_space filter
section
example {α : Type*} (n : α → filter α) (H₀ : ∀ a, pure a ≤ n a) 
  (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → (∀ᶠ y in n a, ∀ᶠ x in n y, p x)) :
  ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' :=
begin
  intros a s s_in,
  refine ⟨{y | s ∈ n y}, H a (λ x, x ∈ s) s_in, _, by tauto⟩,
  rintros y (hy : s ∈ n y),
  exact H₀ y hy
end
end
example {X Y A : Type*} [topological_space X] {c : A → X} {f : A → Y} {x : X} {F : filter Y}
  (h : tendsto f (comap c (𝓝 x)) F) {V' : set Y} (V'_in : V' ∈ F) :
  ∃ V ∈ 𝓝 x, is_open V ∧ c ⁻¹' V ⊆ f ⁻¹' V' :=
begin
  simpa [and_assoc] using ((nhds_basis_opens' x).comap c).tendsto_left_iff.mp h V' V'_in
end


example [topological_space X] [topological_space Y] [regular_space Y] {A : set X} (hA : ∀ x, x ∈ closure A)
  {f : A → Y} (f_cont : continuous f)
  (hf : ∀ x : X, ∃ c : Y, tendsto f (comap coe $ 𝓝 x) $ 𝓝 c) :
  ∃ φ : X → Y, continuous φ ∧ ∀ a : A, φ a = f a :=
begin
  choose φ hφ using hf,
  use φ,
  split,
  { rw continuous_iff_continuous_at,
    intros x,
    suffices : ∀ V' ∈ 𝓝 (φ x), is_closed V' → φ ⁻¹' V' ∈ 𝓝 x,
      by simpa [continuous_at, (closed_nhds_basis _).tendsto_right_iff],
    intros V' V'_in V'_closed,
    obtain ⟨V, V_in, V_op, hV⟩ : ∃ V ∈ 𝓝 x, is_open V ∧ coe ⁻¹' V ⊆ f ⁻¹' V',
    { exact aux (hφ x) V'_in },
    suffices : ∀ y ∈ V, φ y ∈ V',
      from mem_of_superset V_in this,
    intros y y_in,
    have hVx : V ∈ 𝓝 y := V_op.mem_nhds y_in,
    haveI : (comap (coe : A → X) (𝓝 y)).ne_bot := by simpa [mem_closure_iff_comap_ne_bot] using hA y,
    apply V'_closed.mem_of_tendsto (hφ y),
    exact mem_of_superset (preimage_mem_comap hVx) hV },
  { intros a,
    have lim : tendsto f (𝓝 a) (𝓝 $ φ a),
      by simpa [nhds_induced] using hφ a,
    exact tendsto_nhds_unique lim f_cont.continuous_at },
end


example [topological_space Y] {f : X  → Y} (hf : continuous f) 
  {s : set X} (hs : is_compact s) : is_compact (f '' s) :=
begin
  intros F F_ne F_le,
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F,
  { rw [filter.push_pull, map_principal] },
  haveI Hne : (𝓟 s ⊓ comap f F).ne_bot,
  { apply ne_bot.of_map,
    rwa [map_eq, inf_of_le_right F_le] },
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s, from inf_le_left,
  rcases hs Hle with ⟨x, x_in, hx⟩,
  refine ⟨f x, mem_image_of_mem f x_in, _⟩,
  apply hx.map hf.continuous_at,
  rw [tendsto, map_eq],
  exact inf_le_right
end


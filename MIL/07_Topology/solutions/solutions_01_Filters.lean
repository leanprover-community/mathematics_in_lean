import topology.instances.real

open set filter
open_locale topological_space filter

-- In the next example we could use `tauto` in each proof instead of knowing the lemmas
example {α : Type*} (s : set α) : filter α :=
{ sets := {t | s ⊆ t},
  univ_sets := subset_univ s,
  sets_of_superset := λ U V hU hUV, subset.trans hU hUV,
  inter_sets := λ U V hU hV, subset_inter hU hV }

example : filter ℕ :=
{ sets := {s | ∃ a, ∀ b, a ≤ b → b ∈ s},
  univ_sets := begin
    use 42,
    finish,
  end,
  sets_of_superset := begin
    rintros U V ⟨N, hN⟩ hUV,
    use N,
    tauto,
  end,
  inter_sets := begin
    rintros U V ⟨N, hN⟩ ⟨N', hN'⟩,
    use max N N',
    intros b hb,
    rw max_le_iff at hb,
    split ; tauto,
  end }

def tendsto₁ {X Y : Type*} (f : X → Y) (F : filter X) (G : filter Y) :=
∀ V ∈ G, f ⁻¹' V ∈ F

example {X Y Z : Type*} {F : filter X} {G : filter Y} {H : filter Z} {f : X → Y} {g : Y → Z}
  (hf : tendsto₁ f F G) (hg : tendsto₁ g G H) : tendsto₁ (g ∘ f) F H :=
calc map (g ∘ f) F = map g (map f F) : by rw map_map
... ≤ map g G : map_mono hf
... ≤ H : hg

example {X Y Z : Type*} {F : filter X} {G : filter Y} {H : filter Z} {f : X → Y} {g : Y → Z}
  (hf : tendsto₁ f F G) (hg : tendsto₁ g G H) : tendsto₁ (g ∘ f) F H :=
begin
  intros V hV,
  rw preimage_comp,
  apply hf,
  apply hg,
  exact hV
end

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
  tendsto f at_top (𝓝 (x₀, y₀)) ↔
  tendsto (prod.fst ∘ f) at_top (𝓝 x₀) ∧ tendsto (prod.snd ∘ f) at_top (𝓝 y₀) :=
calc
tendsto f at_top (𝓝 (x₀, y₀)) ↔ map f at_top ≤ 𝓝 (x₀, y₀) : iff.rfl
... ↔ map f at_top ≤ 𝓝 x₀ ×ᶠ 𝓝 y₀ : by rw nhds_prod_eq
... ↔ map f at_top ≤ (comap prod.fst (𝓝 x₀) ⊓ comap prod.snd (𝓝 y₀)) : iff.rfl
... ↔ map f at_top ≤ comap prod.fst (𝓝 x₀) ∧ map f at_top ≤ (comap prod.snd (𝓝 y₀)) : le_inf_iff
... ↔ map prod.fst (map f at_top) ≤ 𝓝 x₀ ∧ map prod.snd (map f at_top) ≤ 𝓝 y₀ :
        by rw [← map_le_iff_le_comap, ← map_le_iff_le_comap]
... ↔ map (prod.fst ∘ f) at_top ≤ 𝓝 x₀ ∧ map (prod.snd ∘ f) at_top ≤ 𝓝 y₀ : by rw [map_map, map_map]

-- an alternative solution
example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
  tendsto f at_top (𝓝 (x₀, y₀)) ↔
  tendsto (prod.fst ∘ f) at_top (𝓝 x₀) ∧ tendsto (prod.snd ∘ f) at_top (𝓝 y₀) :=
begin
  rw nhds_prod_eq,
  unfold tendsto filter.prod,
  rw [le_inf_iff, ← map_le_iff_le_comap, map_map, ← map_le_iff_le_comap, map_map]
end

example (u : ℕ → ℝ) (M : set ℝ) (x : ℝ)
  (hux : tendsto u at_top (𝓝 x)) (huM : ∀ᶠ n in at_top, u n ∈ M) : x ∈ closure M :=
mem_closure_iff_cluster_pt.mpr (ne_bot_of_le $ le_inf hux $ le_principal_iff.mpr huM)

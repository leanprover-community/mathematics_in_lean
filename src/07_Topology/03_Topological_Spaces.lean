import topology.instances.real
import analysis.normed_space.banach_steinhaus

open set filter
open_locale topological_space filter


section

variables {X : Type*} [topological_space X]

example : is_open (univ : set X) := is_open_univ

example : is_open (∅ : set X) := is_open_empty

example {ι : Type*} {s : ι → set X} (hs : ∀ i, is_open $ s i) : 
  is_open (⋃ i, s i) := 
is_open_Union hs

example {ι : Type*} [fintype ι] {s : ι → set X} (hs : ∀ i, is_open $ s i) : 
  is_open (⋂ i, s i) := 
is_open_Inter hs




variables {Y : Type*} [topological_space Y]

example {f : X → Y} : continuous f ↔ ∀ s, is_open s → is_open (f ⁻¹' s) :=
continuous_def




example {f : X → Y} {x : X} : continuous_at f x ↔ map f (𝓝 x) ≤ 𝓝 (f x) :=
iff.rfl



example {f : X → Y} {x : X} : continuous_at f x ↔ ∀ U ∈ 𝓝 (f x), ∀ᶠ x in 𝓝 x, f x ∈ U :=
iff.rfl


example {x : X} {s : set X} : s ∈ 𝓝 x ↔ ∃ t ⊆ s, is_open t ∧ x ∈ t :=
mem_nhds_iff


example (x : X) : pure x ≤ 𝓝 x := pure_le_nhds x

example (x : X) (P : X → Prop) (h : ∀ᶠ y in 𝓝 x, P y) : P x := 
pure_le_nhds x h



example {P : X → Prop} {x : X} (h : ∀ᶠ y in 𝓝 x, P y) : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, P z :=
eventually_eventually_nhds.mpr h



#check topological_space.mk_of_nhds
#check topological_space.nhds_mk_of_nhds.


example {α : Type*} (n : α → filter α) (H₀ : ∀ a, pure a ≤ n a) 
  (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → (∀ᶠ y in n a, ∀ᶠ x in n y, p x)) :
  ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' :=
sorry


end
-- BOTH.

variables {X Y : Type*}

example (f : X → Y) : topological_space X → topological_space Y :=
topological_space.coinduced f

example (f : X → Y) : topological_space Y → topological_space X :=
topological_space.induced f

example (f : X → Y) (T_X : topological_space X) (T_Y : topological_space Y) :
  topological_space.coinduced f T_X ≤ T_Y ↔ T_X ≤ topological_space.induced f T_Y :=
coinduced_le_iff_le_induced



#check coinduced_compose
#check induced_compose.


example {T T' : topological_space X} :
  T ≤ T' ↔ ∀ s, T'.is_open s → T.is_open s  :=
iff.rfl



example (T_X : topological_space X) (T_Y : topological_space Y) (f : X → Y) :
  continuous f ↔ topological_space.coinduced f T_X ≤ T_Y :=
continuous_iff_coinduced_le




example {Z : Type*} (f : X → Y) 
  (T_X : topological_space X) (T_Z : topological_space Z) (g : Y → Z) :
  @continuous Y Z (topological_space.coinduced f T_X) T_Z g ↔ @continuous X Z T_X T_Z (g ∘ f) :=
by rw [continuous_iff_coinduced_le, coinduced_compose, continuous_iff_coinduced_le]



example (ι : Type*) (X : ι → Type*) (T_X : Π i, topological_space $ X i) :
  (Pi.topological_space : topological_space (Π i, X i)) = ⨅ i, topological_space.induced (λ x, x i) (T_X i) :=
rfl




example [topological_space X] [t2_space X] {u : ℕ → X} {a b : X} 
  (ha : tendsto u at_top (𝓝 a)) (hb : tendsto u at_top (𝓝 b)) : a = b :=
tendsto_nhds_unique ha hb

example [topological_space X] [regular_space X] (a : X) :
    (𝓝 a).has_basis (λ (s : set X), s ∈ 𝓝 a ∧ is_closed s) id :=
closed_nhds_basis a


example [topological_space X] {x : X} : (𝓝 x).has_basis (λ t : set X, t ∈ 𝓝 x ∧ is_open t) id :=
nhds_basis_opens' x


lemma aux {X Y A : Type*} [topological_space X] {c : A → X} {f : A → Y} {x : X} {F : filter Y}
  (h : tendsto f (comap c (𝓝 x)) F) {V' : set Y} (V'_in : V' ∈ F) :
  ∃ V ∈ 𝓝 x, is_open V ∧ c ⁻¹' V ⊆ f ⁻¹' V' :=
sorry




example [topological_space X] [topological_space Y] [regular_space Y] 
  {A : set X} (hA : ∀ x, x ∈ closure A)
  {f : A → Y} (f_cont : continuous f)
  (hf : ∀ x : X, ∃ c : Y, tendsto f (comap coe $ 𝓝 x) $ 𝓝 c) :
  ∃ φ : X → Y, continuous φ ∧ ∀ a : A, φ a = f a :=
sorry



example [topological_space X] [topological_space.first_countable_topology X] {s : set X} {a : X} :
  a ∈ closure s ↔ ∃ (u : ℕ → X), (∀ n, u n ∈ s) ∧ tendsto u at_top (𝓝 a) :=
mem_closure_iff_seq_limit



variables [topological_space X]

example {F : filter X} {x : X} : cluster_pt x F ↔ ne_bot (𝓝 x ⊓ F) :=
iff.rfl

example {s : set X} : 
  is_compact s ↔ ∀ (F : filter X) [ne_bot F], F ≤ 𝓟 s → ∃ a ∈ s, cluster_pt a F :=
iff.rfl


example [topological_space.first_countable_topology X] 
  {s : set X} {u : ℕ → X} (hs : is_compact s) (hu : ∀ n, u n ∈ s) :
  ∃ (a ∈ s) (φ : ℕ → ℕ), strict_mono φ ∧ tendsto (u ∘ φ) at_top (𝓝 a) :=
hs.tendsto_subseq hu



variables [topological_space Y]

example {x : X} {F : filter X} {G : filter Y} (H : cluster_pt x F)
  {f : X → Y} (hfx : continuous_at f x) (hf : tendsto f F G) :
  cluster_pt (f x) G :=
cluster_pt.map H hfx hf


example [topological_space Y] {f : X  → Y} (hf : continuous f) 
  {s : set X} (hs : is_compact s) : is_compact (f '' s) :=
begin
  intros F F_ne F_le,
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F,
  { sorry },
  haveI Hne : (𝓟 s ⊓ comap f F).ne_bot,
  { sorry },
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s, from inf_le_left,
  sorry
end


example {ι : Type*} {s : set X} (hs : is_compact s)
  (U : ι → set X) (hUo : ∀ i, is_open (U i)) (hsU : s ⊆ ⋃ i, U i) :
  ∃ t : finset ι, s ⊆ ⋃ i ∈ t, U i :=
hs.elim_finite_subcover U hUo hsU



example [compact_space X] : is_compact (univ : set X) :=
compact_univ

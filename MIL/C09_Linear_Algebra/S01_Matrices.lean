import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

import MIL.Common


section matrices

#eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

#eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![4, 6; 8, 10]
/-
* `⬝ᵥ` for `Matrix.dotProduct`
* `*ᵥ` for `Matrix.mulVec`
* `ᵥ*` for `Matrix.vecMul`
* `ᵀ` for `Matrix.transpose`
* `ᴴ` for `Matrix.conjTranspose`

Concrete matrices with concrete entries

Note we are not suggesting to replace Sage with #eval or #norm_num
-/
open Matrix

#eval row (Fin 1) ![1, 2]

#eval col (Fin 1) ![1, 2]

#eval ![1, 2] ⬝ᵥ ![3, 4] -- vector dot product

#eval !![1, 2; 3, 4] *ᵥ ![1, 1]  -- matrices acting on vectors on the left

#eval !![1, 2] *ᵥ ![1, 1]  -- matrices acting on vectors on the left

#eval  ![1, 1, 1] ᵥ* !![1, 2; 3, 4; 5, 6]  -- matrices acting on vectors on the right

#eval !![1, 2; 3, 4]ᵀ

#eval !![(1 : ℤ), 2; 3, 4].det

#simp !![(1 : ℝ), 2; 3, 4].det
#norm_num !![(1 : ℝ), 2; 3, 4].det

-- Marche pas comme on veut
#norm_num !![(1 : ℝ), 2; 3, 4] ⁻¹

example : !![(1 : ℝ), 2; 3, 4].det = -2 := by
  simp only [det_fin_two_of, one_mul]
  norm_num

example : !![(1 : ℝ), 2; 3, 4].trace = 5 := by
  simp [trace]
  norm_num

-- variable {R : Type*} [AddCommMonoid R]
-- @[simp]
-- theorem trace_fin_one_of (a : R) : trace !![a] = a :=
--   trace_fin_one _
--
-- @[simp]
-- theorem trace_fin_two_of (a b c d : R) : trace !![a, b; c, d] = a + d :=
--   trace_fin_two _
--
-- @[simp]
-- theorem trace_fin_three_of (a b c d e f g h i : R) :
--     trace !![a, b, c; d, e, f; g, h, i] = a + e + i :=
--   trace_fin_three _

-- L’exemple ci-dessous est très décevant sans les lemmes ci-dessus (qui sont proposés dans Mathlib)
#norm_num !![(1 : ℝ), 2; 3, 4].trace

variable (a b c d : ℝ) in
#simp !![a, b; c, d].det

-- Discuss inverse of matrix. See     Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean


section

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n]

example (A B : Matrix n n R) : trace (A*B - B*A) = 0 := by
  rw [trace_sub, trace_mul_comm, sub_self]

end
end matrices



variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]


example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
  smul_add a u v

example (a b : K) (u : V) : (a + b) • u = a • u + b • u :=
  add_smul a b u

example (a b : K) (u : V) : a • b • u = b • a • u :=
  smul_comm a b u



variable {W : Type*} [AddCommGroup W] [Module K W]

variable (φ : V →ₗ[K] W)

example (a : K) (v : V) : φ (a • v) = a • φ v :=
  map_smul φ a v

example (v w : V) : φ (v + w) = φ v + φ w :=
  map_add φ v w


variable (ψ : V →ₗ[K] W)

#check (2 • φ + ψ : V →ₗ[K] W)


variable (θ : W →ₗ[K] V)

#check (φ.comp θ : W →ₗ[K] W)
#check (φ ∘ₗ θ : W →ₗ[K] W)


example : V →ₗ[K] V where
  toFun v := 3 • v
  map_add' _ _ := smul_add ..
  map_smul' _ _ := smul_comm ..



#check φ.map_add'
#check φ.map_add
#check map_add φ



#check LinearMap.lsmul K V 3
#check LinearMap.lsmul K V


example (f : V ≃ₗ[K] W) :
    f ≪≫ₗ f.symm = LinearEquiv.refl K V :=
  f.self_trans_symm

noncomputable example (f : V →ₗ[K] W) (h : Function.Bijective f) : V ≃ₗ[K] W :=
  .ofBijective f h

section binary_product

variable {W : Type*} [AddCommGroup W] [Module K W]
variable {U : Type*} [AddCommGroup U] [Module K U]
variable {T : Type*} [AddCommGroup T] [Module K T]

-- First projection map
example : V × W →ₗ[K] V := LinearMap.fst K V W

-- Second projection map
example : V × W →ₗ[K] W := LinearMap.snd K V W

-- Universal property of the product
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : U →ₗ[K]  V × W := LinearMap.prod φ ψ

-- The product map does the expected thing, first component
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.fst K V W ∘ₗ LinearMap.prod φ ψ = φ := rfl

-- The product map does the expected thing, second component
example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.snd K V W ∘ₗ LinearMap.prod φ ψ = ψ := rfl

-- We can also combine maps in parallel
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) : (V × W) →ₗ[K] (U × T) := φ.prodMap ψ

-- This is simply done by combining the projections with the universal property
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) :
  φ.prodMap ψ = (φ ∘ₗ .fst K V W).prod (ψ ∘ₗ.snd K V W) := rfl

-- First inclusion map
example : V →ₗ[K] V × W := LinearMap.inl K V W

-- Second inclusion map
example : W →ₗ[K] V × W := LinearMap.inr K V W

-- Universal property of the sum (aka coproduct)
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : V × W →ₗ[K] U := φ.coprod ψ

-- The coproduct map does the expected thing, first component
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inl K V W = φ :=
  LinearMap.coprod_inl φ ψ

-- The coproduct map does the expected thing, second component
example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inr K V W = ψ :=
  LinearMap.coprod_inr φ ψ



end binary_product


section families
open DirectSum

variable {ι : Type*} [DecidableEq ι] (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

example (φ : Π i, V i →ₗ[K] W) : (⨁ i, V i) →ₗ[K] W :=
  DirectSum.toModule K ι W φ


example (φ : Π i, W →ₗ[K] V i) : W →ₗ[K] (Π i, V i) :=
  LinearMap.pi φ

example (i : ι) : (Π j, V j) →ₗ[K] V i := LinearMap.proj i

example : Π i, V i →+ (⨁ i, V i) := DirectSum.of V

example : Π i, V i →ₗ[K] (⨁ i, V i) := DirectSum.lof K ι V

variable (i : ι) in
#check LinearMap.single (R := K) (φ := V) i  -- The linear inclusion of V i into the product

variable (i : ι) in
#check DirectSum.lof K ι V i -- The linear inclusion of V i into the sum

example [Fintype ι] : (⨁ i, V i) ≃ₗ[K] (Π i, V i) :=
  linearEquivFunOnFintype K ι V

end families


example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
    x + y ∈ U :=
  U.add_mem hx hy

example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
    a • x ∈ U :=
  U.smul_mem a hx


noncomputable example : Submodule ℝ ℂ where
  carrier := Set.range ((↑) : ℝ → ℂ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  smul_mem' := by
    rintro c - ⟨a, rfl⟩
    use c*a
    simp


def preimage (φ : V →ₗ[K] W) (H : Submodule K W) : Submodule K V where
  carrier := φ ⁻¹' H
  zero_mem' := by
    dsimp
    sorry
  add_mem' := by
    sorry
  smul_mem' := by
    dsimp
    sorry

example (U : Submodule K V) : Module K U := inferInstance

example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance

example (H H' : Submodule K V) :
    ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl

example (H H' : Submodule K V) :
    ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
  simp [Submodule.span_union]

example (x : V) : x ∈ (⊤ : Submodule K V) := trivial

example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K

example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊔ V = ⊤ := h.sup_eq_top

example (U V : Submodule K V) (h : IsCompl U V) :
  U ⊓ V = ⊥ := h.inf_eq_bot

#check DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top

example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
  ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
    {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
  h.submodule_independent.pairwiseDisjoint hij |>.eq_bot

variable (E : Submodule K V) in
#check Submodule.map φ E

variable (F : Submodule K W) in
#check Submodule.comap φ F
example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ

example : LinearMap.ker φ = .comap φ ⊥ := rfl


open Function LinearMap

example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm

#check Submodule.mem_map_of_mem
#check Submodule.mem_map
#check Submodule.mem_comap

example (E : Submodule K V) (F : Submodule K W) :
    Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
    dsimp
    sorry

variable (E : Submodule K V)

example : Module K (V ⧸ E) := inferInstance

example : V →ₗ[K] V ⧸ E := E.mkQ

example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange

variable {ι : Type*} (B : Basis ι K V) (v : V) (i : ι)

-- The basis vector with index ``i``
#check B i -- V

-- the linear isomorphism with the model space given by ``B``
#check B.repr -- V ≃ₗ[K] ι →₀ K

-- the component function of ``v``
#check B.repr v -- ι →₀ K

-- the component of ``v`` with index ``i``
#check B.repr v i -- K


variable [DecidableEq ι]

example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
  rfl

example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
  rfl

#check Finsupp.basisSingleOne

#check Pi.basisFun

example (i : ι) : Finsupp.basisSingleOne i = Finsupp.single i 1 :=
  rfl


open PiNotation
#check LinearMap.stdBasis K (fun _ : ι ↦ K)

/-

* `Basis.constr b R f` constructs a linear map `M₁ →ₗ[R] M₂` given the values `f : ι → M₂` at the
  basis elements `⇑b : ι → M₁`.
* `Basis.reindex` uses an equiv to map a basis to a different indexing set.
* `Basis.map` uses a linear equiv to map a basis to a different module.

## Main statements

* `Basis.mk`: a linear independent set of vectors spanning the whole module determines a basis

* `Basis.ext` states that two linear maps are equal if they coincide on a basis.
  Similar results are available for linear equivs (if they coincide on the basis vectors),
  elements (if their coordinates coincide) and the functions `b.repr` and `⇑b`.


Bases, representing vectors and linear maps in a basis

Dimension

Endomorphisms (polynomial evaluation, minimal polynomial, Caley-Hamilton,
eigenvalues, eigenvectors)

Multilinear algebra (multilinear maps, alternating maps, quadratic forms,
inner products, matrix representation, spectral theorem, tensor products)

Modules over rings


in Mathlib/RingTheory/Ideal/Operations.lean:
instance Submodule.moduleSubmodule {R : Type u} {M : Type v} [CommSemiring R] [AddCommMonoid M] [Module R M] :
Module (Ideal R) (Submodule R M)

-/

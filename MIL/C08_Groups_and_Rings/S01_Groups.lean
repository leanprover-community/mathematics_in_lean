import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.PresentedGroup

import MIL.Common

example {M : Type*} [Monoid M] (x : M) : x*1 = x := mul_one x

example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
f.map_mul x y

example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
f.map_zero

example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
  (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f

example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_self x

example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x*z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
  group

example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
  abel

example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
f.map_mul x y

example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
f.map_inv x

example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
  G →* H :=
MonoidHom.mk' f h

example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
  f.trans f.symm = MulEquiv.refl G :=
f.self_trans_symm

noncomputable example {G H : Type*} [Group G] [Group H]
      (f : G →* H) (h : Function.Bijective f) :
    G ≃* H :=
  MulEquiv.ofBijective f h

example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
  x * y ∈ H :=
H.mul_mem hx hy

example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
  x⁻¹ ∈ H :=
H.inv_mem hx

example : AddSubgroup ℚ where
  carrier := Set.range ((↑) : ℤ → ℚ)
  add_mem' := by
    rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
    use n + m
    simp
  zero_mem' := by
    use 0
    simp
  neg_mem' := by
    rintro _ ⟨n, rfl⟩
    use -n
    simp

example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance

example {G : Type*} [Group G] (H H' : Subgroup G) :
  ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl

example {G : Type*} [Group G] (H H' : Subgroup G) :
    ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
  rw [Subgroup.sup_eq_closure]

example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial

example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot

def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
  carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
  one_mem' := by
    dsimp
    -- aesop?
    rename_i inst
    exact ⟨1, one_mem H, by simp⟩
  inv_mem' := by
    dsimp
    sorry
  mul_mem' := by
    dsimp
    -- aesop?
    rename_i inst
    intro a b a_1 a_2
    unhygienic with_reducible aesop_destruct_products
    aesop_subst [right_1, right]
    simp_all only [conj_mul, mul_left_inj, mul_right_inj, exists_eq_right']
    apply MulMemClass.mul_mem
    · simp_all only
    · simp_all only

example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
  Subgroup.map f G'

example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
  Subgroup.comap f H'

#check Subgroup.mem_map
#check Subgroup.mem_comap

example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
    g ∈ MonoidHom.ker f ↔ f g = 1 :=
  f.mem_ker

example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
    h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
  f.mem_range

section exercises
variable {G H : Type*} [Group G] [Group H]

open Subgroup

example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
  -- suggest_tactics
  -- aesop?
  rename_i inst inst_1
  exact comap_mono hST

example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
  -- suggest_tactics
  -- aesop?
  rename_i inst inst_1
  convert map_mono hST

variable {K : Type*} [Group K]

-- Remember you can use the `ext` tactic to prove an equality of subgroups.
example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
  comap (ψ.comp φ) U = comap φ (comap ψ U) := by
  -- suggest_tactics
  -- aesop?
  rename_i inst inst_1 inst_2
  apply Eq.refl

-- Pushing a subgroup along one homomorphism and then another is equal to
--  pushing it forward along the composite of the homomorphisms.
example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
  map (ψ.comp φ) S = map ψ (S.map φ) := by
  -- aesop?
  rename_i inst inst_1 inst_2
  ext <;> simp

end exercises

attribute [local instance 10] setFintype Classical.propDecidable

open Fintype

example {G : Type*} [Group G] [Fintype G] (G' : Subgroup G) : card G' ∣ card G :=
  ⟨G'.index, mul_comm G'.index _ ▸ G'.index_mul_card.symm⟩

open Subgroup

example {G : Type*} [Group G] [Fintype G] (p : ℕ) {n : ℕ} [Fact p.Prime]
    (hdvd : p ^ n ∣ card G) : ∃ K : Subgroup G, card K = p ^ n :=
  Sylow.exists_subgroup_card_pow_prime p hdvd

-- [EXCEPTION] aesop generates a buggy proof.  (Peiyang)
lemma eq_bot_iff_card {G : Type*} [Group G] {H : Subgroup G} [Fintype H] :
    H = ⊥ ↔ card H = 1 := by
  suffices (∀ x ∈ H, x = 1) ↔ ∃ x ∈ H, ∀ a ∈ H, a = x by
    simpa [eq_bot_iff_forall, card_eq_one_iff]
  -- aesop?
  rename_i inst inst_1
  apply Iff.intro
  · intro a
    simp_all only
    apply Exists.intro
    apply And.intro
    on_goal 2 => intro a_1 a_2
    on_goal 2 => apply Eq.refl
    apply OneMemClass.one_mem
  · intro a x a_1
    unhygienic with_reducible aesop_destruct_products
    simp_all only
    symm
    apply right
    apply OneMemClass.one_mem

#check card_dvd_of_le

lemma inf_bot_of_coprime {G : Type*} [Group G] (H K : Subgroup G) [Fintype H] [Fintype K]
    (h : (card H).Coprime (card K))  : H ⊓ K = ⊥ := by
    sorry
open Equiv

example {X : Type*} [Finite X] : Subgroup.closure {σ : Perm X | Perm.IsCycle σ} = ⊤ :=
Perm.closure_isCycle

#simp [mul_assoc] c[1, 2, 3] * c[2, 3, 4]

section FreeGroup

inductive S | a | b | c

open S

def myElement : FreeGroup S := (.of a) * (.of b)⁻¹

def myMorphism : FreeGroup S →* Perm (Fin 5) :=
  FreeGroup.lift fun | .a => c[1, 2, 3]
                     | .b => c[2, 3, 1]
                     | .c => c[2, 3]


def myGroup := PresentedGroup {.of () ^ 3} deriving Group

def myMap : Unit → Perm (Fin 5)
| () => c[1, 2, 3]

lemma compat_myMap :
    ∀ r ∈ ({.of () ^ 3} : Set (FreeGroup Unit)), FreeGroup.lift myMap r = 1 := by
  rintro _ rfl
  simp

def myNewMorphism : myGroup →* Perm (Fin 5) := PresentedGroup.toGroup compat_myMap

end FreeGroup

noncomputable section GroupActions

example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
  g • (g' • x) = (g * g') • x :=
(mul_smul g g' x).symm

example {G X : Type*} [AddGroup G] [AddAction G X] (g g' : G) (x : X) :
  g +ᵥ (g' +ᵥ x) = (g + g') +ᵥ x :=
(add_vadd g g' x).symm

open MulAction

example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
toPermHom G X

def CayleyIsoMorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range :=
Equiv.Perm.subgroupOfMulAction G G

example {G X : Type*} [Group G] [MulAction G X] :
    X ≃ (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out' ω)) :=
  MulAction.selfEquivSigmaOrbits G X

example {G X : Type*} [Group G] [MulAction G X] (x : X) :
    orbit G x ≃ G ⧸ stabilizer G x :=
  MulAction.orbitEquivQuotientStabilizer G x

example {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
  groupEquivQuotientProdSubgroup

variable {G : Type*} [Group G]

lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
    -- suggest_tactics
    -- aesop?
    rename_i inst
    rw [conjugate_one]

instance : MulAction G (Subgroup G) where
  smul := conjugate
  one_smul := by
    sorry
  mul_smul := by
    sorry

end GroupActions

noncomputable section QuotientGroup

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
QuotientGroup.mk' H

example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
  [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
QuotientGroup.lift N φ h

example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
    G ⧸ MonoidHom.ker φ →* MonoidHom.range φ :=
  QuotientGroup.quotientKerEquivRange φ

example {G G': Type*} [Group G] [Group G']
    {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
    {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G' ⧸ N':=
  QuotientGroup.map N N' φ h

example {G : Type*} [Group G] {M N : Subgroup G} [M.Normal]
  [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N := QuotientGroup.quotientMulEquivOfEq  h

section
variable  {G : Type*} [Group G] {H K : Subgroup G}

open MonoidHom

#check card_pos -- The nonempty argument will be automatically inferred for subgroups
#check Subgroup.index_eq_card
#check Subgroup.index_mul_card
#check Nat.eq_of_mul_eq_mul_right

lemma aux_card_eq [Fintype G] (h' : card G = card H * card K) : card (G⧸H) = card K := by
  sorry
variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K) (h' : card G = card H * card K)

#check bijective_iff_injective_and_card
#check ker_eq_bot_iff
#check restrict
#check ker_restrict

def iso₁ [Fintype G] (h : Disjoint H K) (h' : card G = card H * card K) : K ≃* G⧸H := by
  sorry
def iso₂ : G ≃* (G⧸K) × (G⧸H) := by
  sorry
#check MulEquiv.prodCongr

def finalIso : G ≃* H × K :=
  sorry

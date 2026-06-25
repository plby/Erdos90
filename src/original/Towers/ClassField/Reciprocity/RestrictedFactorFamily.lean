import Mathlib.Algebra.BigOperators.Finprod
import Towers.ClassField.Reciprocity.ArtinMapStatements

/-!
# Chapter V, Section 5, Proposition 5.2

Milne constructs the finite-layer Artin map as the product of its local
components, observes that only finitely many factors are nontrivial, and then
passes through the inverse limit of all finite abelian subextensions.

This file formalizes the two algebraic parts of that argument which do not
depend on unimplemented arithmetic:

* an eventually-unit-trivial family of local homomorphisms has a canonical
  homomorphism on a restricted product, given by `finprod`; and
* a pointwise compatible family of finite-layer products assembles uniquely
  into the absolute abelian Galois group.

The remaining inputs are named narrowly.  `LASystem`
asks for the actual local reciprocity products, their finite-layer uniqueness
and continuity, and their pointwise inverse-limit compatibility.
`RestrictionTopologyInterface` is exactly the missing assertion that
continuity into the profinite absolute abelian Galois group can be checked on
all finite restrictions.  No reciprocity or existence theorem is assumed.
-/

namespace Towers.CField.Recip

open Filter IsDedekindDomain NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open scoped RestrictedProduct

noncomputable section

universe u v w

section RestrictedLocalProduct

variable {ι : Type u} {G : ι → Type v} [∀ i, CommGroup (G i)]
variable (U : ∀ i, Subgroup (G i))
variable {A : Type w} [CommGroup A]

/-- A family of local homomorphisms which kills the distinguished local unit
subgroups at all but finitely many indices.  This is the exact finiteness
condition used in the source to define a product of local Artin symbols. -/
structure RLFam where
  localHom : ∀ i, G i →* A
  eventually_units :
    ∀ᶠ i in cofinite, ∀ x : G i, x ∈ U i → localHom i x = 1

namespace RLFam

variable (D : RLFam (A := A) U)

/-- For a restricted-product element, only finitely many local factors are
nontrivial. -/
theorem finite_mulSupport (x : Πʳ i, [G i, U i]) :
    Function.HasFiniteMulSupport (fun i => D.localHom i (x i)) := by
  change {i | D.localHom i (x i) ≠ 1}.Finite
  rw [← eventually_cofinite]
  filter_upwards [x.2, D.eventually_units] with i hxi hi
  simpa using hi (x i) hxi

/-- The product of the local factors.  `finprod` is legitimate by
`finite_mulSupport`; unlike an arbitrary infinite product, it is purely the
finite product appearing in Milne's proof. -/
def restrictedProductHom :
    (Πʳ i, [G i, U i]) →* A where
  toFun x := ∏ᶠ i, D.localHom i (x i)
  map_one' := by
    apply finprod_eq_one_of_forall_eq_one
    intro i
    exact map_one (D.localHom i)
  map_mul' x y := by
    rw [show (∏ᶠ i, D.localHom i ((x * y) i)) =
        ∏ᶠ i, D.localHom i (x i) * D.localHom i (y i) by
      apply finprod_congr
      intro i
      exact map_mul (D.localHom i) (x i) (y i)]
    exact finprod_mul_distrib (finite_mulSupport (U := U) D x)
      (finite_mulSupport (U := U) D y)

/-- The restricted product homomorphism has the prescribed value on a
one-coordinate element. -/
theorem restricted_product_single [DecidableEq ι]
    (i : ι) (x : G i) :
    D.restrictedProductHom U (RestrictedProduct.mulSingle U i x) =
      D.localHom i x := by
  change (∏ᶠ j, D.localHom j
      ((RestrictedProduct.mulSingle U i x) j)) = D.localHom i x
  calc
    _ = D.localHom i ((RestrictedProduct.mulSingle U i x) i) := by
      apply finprod_eq_single _ i
      intro j hji
      rw [RestrictedProduct.mulSingle_eq_of_ne U x hji]
      exact map_one (D.localHom j)
    _ = D.localHom i x := by
      rw [RestrictedProduct.mulSingle_eq_same]

end RLFam

end RestrictedLocalProduct

variable {K : Type u} [Field K] [NumberField K]

local notation "𝓞K" => NumberField.RingOfIntegers K

noncomputable local instance restrictedLocalFactorFamilyFiniteLayerNumberField
    (L : FASubext K) : NumberField L.1 :=
  NumberField.of_module_finite K L.1

/-- The local-product property for a homomorphism to one finite abelian
layer.  It is exactly the `L`-component of `GlobalArtin`, with no global
map or additional hypothesis hidden in the definition. -/
def LayerArtinProduct
    (L : FASubext K)
    (f : IdeleGroup 𝓞K K →* Gal(L.1/K)) : Prop :=
  (∀ (P : HeightOneSpectrum 𝓞K)
      (Q : UpperPrimeFactors (K := K) (L := L.1) P),
    ∃ phi_v : (P.adicCompletion K)ˣ →* Gal(L.1/K),
      LayerLocalArtin L P Q phi_v ∧
      ∀ x : (P.adicCompletion K)ˣ,
        f (finitePlaceEmbedding 𝓞K K P x) = phi_v x) ∧
  ∀ (v : InfinitePlace K)
      (w : InfinitePlacesAbove (K := K) (L := L.1) v),
    ∃ phi_v : v.1.Completionˣ →* Gal(L.1/K),
      InfiniteLayerArtin L v w phi_v ∧
      ∀ x : v.1.Completionˣ,
        f (infinitePlaceEmbedding 𝓞K K v x) = phi_v x

/-- The global local-compatibility predicate is precisely the assertion that
every finite restriction is its finite-layer local product. -/
theorem global_artin_products
    (phi : IdeleGroup 𝓞K K →* AbsoluteAbelianGalois K) :
    GlobalArtin phi ↔
      ∀ L : FASubext K,
        LayerArtinProduct L ((localAbelianRestriction L).comp phi) := by
  constructor
  · rintro ⟨hfinite, hinfinite⟩ L
    exact ⟨hfinite L, hinfinite L⟩
  · intro h
    exact ⟨fun L => (h L).1, fun L => (h L).2⟩

set_option maxHeartbeats 4000000 in
-- Descending Krull-continuous restriction through the topological
-- abelianization quotient is elaboration-heavy.
omit [NumberField K] in
theorem continuous_abelian_restriction
    (L : FASubext K) :
    Continuous (localAbelianRestriction L) := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  exact InfiniteGalois.restrictNormalHom_continuous
    (k := K) (K := SeparableClosure K) L.finiteIntermediateField

/-- The precise finite-layer and inverse-limit data used in the proof of
Proposition V.5.2.

`pointwise_inverseLimit` says exactly that a compatible tuple of all finite
Artin products is represented by a unique element of the absolute abelian
Galois group.  Thus it isolates the absent global profinite inverse-limit
interface rather than assuming the desired global homomorphism. -/
structure LASystem where
  layerMap (L : FASubext K) :
    IdeleGroup 𝓞K K →* Gal(L.1/K)
  layer_local_product (L : FASubext K) :
    LayerArtinProduct L (layerMap L)
  layer_unique (L : FASubext K)
      (f : IdeleGroup 𝓞K K →* Gal(L.1/K)) :
    Continuous f → LayerArtinProduct L f → f = layerMap L
  layer_continuous (L : FASubext K) :
    Continuous (layerMap L)
  pointwise_inverseLimit (a : IdeleGroup 𝓞K K) :
    ∃! sigma : AbsoluteAbelianGalois K,
      ∀ L : FASubext K,
        localAbelianRestriction L sigma = layerMap L a

namespace LASystem

variable (D : LASystem (K := K))

/-- The inverse-limit value represented by the compatible finite products. -/
def limitValue (a : IdeleGroup 𝓞K K) :
    AbsoluteAbelianGalois K :=
  Classical.choose (D.pointwise_inverseLimit a)

theorem limitValue_spec (a : IdeleGroup 𝓞K K)
    (L : FASubext K) :
    localAbelianRestriction L (D.limitValue a) = D.layerMap L a :=
  (Classical.choose_spec (D.pointwise_inverseLimit a)).1 L

theorem limitValue_unique (a : IdeleGroup 𝓞K K)
    (sigma : AbsoluteAbelianGalois K)
    (hsigma : ∀ L : FASubext K,
      localAbelianRestriction L sigma = D.layerMap L a) :
    sigma = D.limitValue a :=
  (Classical.choose_spec (D.pointwise_inverseLimit a)).2 sigma hsigma

/-- Assemble the finite products into a homomorphism to the absolute
abelian Galois group.  Multiplicativity follows from uniqueness in the
inverse limit, not from an additional assumption. -/
def assemble :
    IdeleGroup 𝓞K K →* AbsoluteAbelianGalois K where
  toFun := D.limitValue
  map_one' := by
    symm
    apply D.limitValue_unique 1 1
    intro L
    simp
  map_mul' a b := by
    symm
    apply D.limitValue_unique (a * b) (D.limitValue a * D.limitValue b)
    intro L
    rw [map_mul, D.limitValue_spec, D.limitValue_spec, map_mul]

/-- Every finite restriction of the assembled map is the prescribed finite
product. -/
theorem restriction_assemble (L : FASubext K) :
    (localAbelianRestriction L).comp D.assemble = D.layerMap L := by
  apply MonoidHom.ext
  intro a
  exact D.limitValue_spec a L

/-- The assembled map has all of the local compatibility squares in the
literal statement of Proposition V.5.2. -/
theorem global_artin_assemble : GlobalArtin D.assemble := by
  rw [global_artin_products]
  intro L
  rw [D.restriction_assemble]
  exact D.layer_local_product L

set_option maxHeartbeats 1000000 in
-- Continuity through the abelianization quotient unfolds the Krull topology.
/-- Any continuous homomorphism satisfying the same local Artin squares
equals the inverse-limit assembly.  Continuity is used only to invoke the
finite-layer product uniqueness theorem. -/
theorem assemble_unique
    (phi : IdeleGroup 𝓞K K →* AbsoluteAbelianGalois K)
    (hphi : ContinuousGlobalArtin phi) :
    phi = D.assemble := by
  ext a
  apply D.limitValue_unique a (phi a)
  intro L
  have hlocal : LayerArtinProduct L
      ((localAbelianRestriction L).comp phi) :=
    (global_artin_products phi).mp hphi.2 L
  have hcontinuous : Continuous
      ((localAbelianRestriction L).comp phi) :=
    (continuous_abelian_restriction L).comp hphi.1
  have heq := D.layer_unique L
    ((localAbelianRestriction L).comp phi) hcontinuous hlocal
  exact DFunLike.congr_fun heq a

end LASystem

/-- The topological inverse-limit interface used in the last sentence of
Milne's proof: a homomorphism to the absolute abelian Galois group is
continuous when all its finite restrictions are continuous. -/
def RestrictionTopologyInterface : Prop :=
  ∀ phi : IdeleGroup 𝓞K K →* AbsoluteAbelianGalois K,
    (∀ L : FASubext K,
      Continuous ((localAbelianRestriction L).comp phi)) →
    Continuous phi

/-- Proposition V.5.2 follows from the concrete finite local products and
the two exact inverse-limit interfaces above. -/
theorem restrictedFamilyStatement
    (D : LASystem (K := K))
    (hTopology : RestrictionTopologyInterface (K := K)) :
    GlobalArtinProposition (K := K) := by
  refine ⟨D.assemble, ?_, ?_⟩
  · constructor
    · apply hTopology D.assemble
      intro L
      rw [D.restriction_assemble]
      exact D.layer_continuous L
    · exact D.global_artin_assemble
  · intro phi hphi
    exact D.assemble_unique phi hphi

end

end Towers.CField.Recip

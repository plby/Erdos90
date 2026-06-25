import Towers.ClassField.Reciprocity.DecompositionGroups
import Towers.ClassField.Reciprocity.CompletionPlaceConjugation
import Towers.NumberTheory.Galois.DecompositionGroup
import Towers.NumberTheory.Galois.PlaceCompletionDegree
import Towers.ClassField.LocalReciprocity.LocalUnitsRep
import Towers.ClassField.Ideles.FinitePlaceCompletion
import Towers.ClassField.IdeleCohomology.CompletionProductAction
import Towers.ClassField.NormIndex.CompletionPlaceBridge
import Towers.ClassField.BrauerLocalization.InfiniteTateZero

/-!
# Chapter V, Section 5, Lemma 5.1 (source statement)

Let `P` and `Q` be primes of the integral closure lying over the same prime
downstairs.  Their decomposition groups are their stabilizers in the global
Galois group.  Galois transitivity gives `Q = σ • P`, and the standard
stabilizer formula gives

`D(Q) = σ D(P) σ⁻¹`.

For an abelian extension conjugation is trivial, so the two decomposition
groups are equal.  The same calculation proves independence of the local
Artin homomorphism once one uses its functoriality under the isomorphism of
completions induced by `σ`.

The canonical finite local Artin map at a completed finite place is built
below from the unconditional norm-residue equivalence of Theorem III.3.1.
At an infinite place, the norm quotient and the decomposition group have the
same cardinality by the archimedean relative-Brauer calculation; both have
order one or two, so the cyclic-group comparison supplies the norm-residue
equivalence.  Thus both the finite and infinite maps are constructed here.

Conjugation extends to an algebra equivalence of completions, intertwines
their decomposition-group identifications, and transports the finite Artin
map by global conjugation.  Since the global Galois group is abelian, the
transported map is unchanged.  At infinity, equality of the norm ranges and
decomposition groups, together with uniqueness of an equivalence between
groups of order at most two, gives independence for arbitrary upper places.
The final number-field source statement has no compatibility hypothesis.
-/

namespace Towers.CField.Recip

open AbsoluteValue IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LRecip
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.ICohomo
open Towers.CField.GWang
open Towers.CField.HNorm
open Towers.CField.BLoc
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

set_option maxHeartbeats 3000000 in
-- The completed extension and Theorem III.3.1 have deeply dependent instances.
set_option synthInstance.maxHeartbeats 1000000 in
-- Typeclass search must assemble the local-field and completed Galois structures.
/-- The canonical finite local Artin homomorphism of Theorem III.3.1 at a
completed finite place, embedded in the ambient global Galois group. -/
noncomputable def globalArtinHom
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    (FinitePlace.mk P).val.Completionˣ →* Gal(L/K) := by
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let e := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun sigma tau ↦ ?_⟩⟩
    apply e.symm.injective
    simpa only [map_mul] using mul_comm (e.symm sigma) (e.symm tau)
  let localArtin : v.Completionˣ →* Gal(w.1.Completion/v.Completion) :=
    (abelianLocalArtin
      v.Completion w.1.Completion).toMonoidHom.comp
        (QuotientGroup.mk'
          (Towers.CField.LFTheory.normSubgroup
            v.Completion w.1.Completion))
  exact completionArtinGlobal v w localArtin

/-- The same completed finite local Artin map, with the source transported
to the prime-adic completion used by the idèle restricted product. -/
noncomputable def adicGlobalArtin
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    (P.adicCompletion K)ˣ →* Gal(L/K) :=
  (globalArtinHom P w).comp
    (Units.map
      (placeCompletionAdic P).symm.toRingHom)

set_option maxHeartbeats 3000000 in
-- The completed extension and Theorem III.3.1 have deeply dependent instances.
set_option synthInstance.maxHeartbeats 1000000 in
-- Typeclass search must assemble the local-field and completed Galois structures.
/-- The canonical finite local Artin map at `w`, transported along the
completion isomorphism to the conjugate place `sigma • w` and then embedded
in the ambient global Galois group. -/
noncomputable def conjugateGlobalArtin
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (sigma : Gal(L/K)) :
    (FinitePlace.mk P).val.Completionˣ →* Gal(L/K) := by
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Fact (AbsoluteValue.LiesOver (sigma • w).1 v) := ⟨(sigma • w).2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra v.Completion (sigma • w).1.Completion :=
    (completionLies v (sigma • w).1 (sigma • w).2).toAlgebra
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let e := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun tau rho ↦ ?_⟩⟩
    apply e.symm.injective
    simpa only [map_mul] using mul_comm (e.symm tau) (e.symm rho)
  let localArtin : v.Completionˣ →* Gal(w.1.Completion/v.Completion) :=
    (abelianLocalArtin
      v.Completion w.1.Completion).toMonoidHom.comp
        (QuotientGroup.mk'
          (Towers.CField.LFTheory.normSubgroup
            v.Completion w.1.Completion))
  exact completionArtinGlobal v (sigma • w)
    (conjugateCompletionArtin v w sigma localArtin)

set_option maxHeartbeats 3000000 in
-- Unfolding the two completion-level Artin constructions is elaboration-heavy.
set_option synthInstance.maxHeartbeats 1000000 in
-- Typeclass search reconstructs the same completed Galois extension on both sides.
/-- The canonical finite local Artin maps at conjugate completed places have
the same image in an abelian global Galois group. -/
theorem artin_independent_conjugate
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (sigma : Gal(L/K)) :
    conjugateGlobalArtin P w sigma =
      globalArtinHom P w := by
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Fact (AbsoluteValue.LiesOver (sigma • w).1 v) := ⟨(sigma • w).2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Algebra v.Completion (sigma • w).1.Completion :=
    (completionLies v (sigma • w).1 (sigma • w).2).toAlgebra
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let e := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun tau rho ↦ ?_⟩⟩
    apply e.symm.injective
    simpa only [map_mul] using mul_comm (e.symm tau) (e.symm rho)
  let localArtin : v.Completionˣ →* Gal(w.1.Completion/v.Completion) :=
    (abelianLocalArtin
      v.Completion w.1.Completion).toMonoidHom.comp
        (QuotientGroup.mk'
          (Towers.CField.LFTheory.normSubgroup
            v.Completion w.1.Completion))
  change completionArtinGlobal v (sigma • w)
      (conjugateCompletionArtin v w sigma localArtin) =
    completionArtinGlobal v w localArtin
  rw [artin_conjugation_compatibility]
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  rw [mul_comm sigma (completionArtinGlobal v w localArtin x),
    mul_inv_cancel_right]

set_option maxHeartbeats 6000000 in
-- The norm quotient, relative Brauer group, and completed decomposition group
-- carry several dependent algebra and Galois instances simultaneously.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The archimedean norm-residue equivalence at an actual infinite place.

The norm quotient is identified with degree-two cohomology and hence with the
relative Brauer group.  Its cardinality is the completed local degree, which
is also the cardinality of the decomposition group.  Both groups have order
one or two, so they are cyclic and the cyclic-cardinality comparison gives
the required multiplicative equivalence. -/
noncomputable def infinitePlaceArtin
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    (v.1.Completionˣ ⧸
        (infiniteCompletionNorm (K := K) (L := L) v w).range) ≃*
      absoluteValueDecomposition v.1 w.1.1 := by
  let hwv := infinite_lies_comap v w.1 w.2
  letI : Fact (AbsoluteValue.LiesOver w.1.1 v.1) := ⟨hwv⟩
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1 hwv).toAlgebra
  letI : FiniteDimensional v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  letI : IsGalois v.1.Completion w.1.1.Completion :=
    infiniteHasseGalois K L v w
  let D := absoluteValueDecomposition v.1 w.1.1
  have hstabilizer : D = MulAction.stabilizer Gal(L/K) w.1 := by
    change absoluteValueDecomposition v.1 w.1.1 = _
    rw [absolute_decomposition_stabilizer]
    ext sigma
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      apply InfinitePlace.ext
      exact fun x ↦ DFunLike.congr_fun h x
    · intro h
      exact congrArg (fun z : InfinitePlace L ↦ z.1) h
  have hDcases : Nat.card D = 1 ∨ Nat.card D = 2 := by
    rw [hstabilizer]
    exact InfinitePlace.nat_card_stabilizer_eq_one_or_two K w.1
  have hDdiv : Nat.card D ∣ 2 := by
    rcases hDcases with hD | hD
    · rw [hD]
      norm_num
    · rw [hD]
  letI : IsCyclic D := isCyclic_of_card_dvd_prime hDdiv
  have hlocalCyclic : IsCyclic Gal(w.1.1.Completion/v.1.Completion) :=
    (infiniteDecompositionGroup v w.1).isCyclic.mp inferInstance
  let eRelative : Additive
      (v.1.Completionˣ ⧸ normSubgroup v.1.Completion w.1.1.Completion) ≃+
      Additive (Towers.CField.BGroups.relativeBrauerGroup
        v.1.Completion w.1.1.Completion) :=
    (hasseGlobal2
      v.1.Completion w.1.1.Completion hlocalCyclic).trans
        (relativeBrauer2
          v.1.Completion w.1.1.Completion).symm
  have hcard : Nat.card
      (v.1.Completionˣ ⧸ normSubgroup v.1.Completion w.1.1.Completion) =
      Nat.card D := by
    calc
      _ = Nat.card
          (Towers.CField.BGroups.relativeBrauerGroup
            v.1.Completion w.1.1.Completion) :=
        Nat.card_congr eRelative.toEquiv
      _ = Module.finrank v.1.Completion w.1.1.Completion :=
        infinite_relative_finrank v w
      _ = Nat.card D :=
        infiniteDegreeCompatibility K L v w
  letI : IsCyclic
      (v.1.Completionˣ ⧸ normSubgroup v.1.Completion w.1.1.Completion) :=
    isCyclic_of_card_dvd_prime (hcard ▸ hDdiv)
  change (v.1.Completionˣ ⧸
      normSubgroup v.1.Completion w.1.1.Completion) ≃* D
  exact mulEquivOfCyclicCardEq hcard

/-- Two multiplicative equivalences into a group of order at most two are
equal.  In the order-two case both carry every nonidentity element to the
unique nonidentity element. -/
theorem card_or_two
    {A B : Type*} [Group A] [Group B]
    (hB : Nat.card B = 1 ∨ Nat.card B = 2)
    (e f : A ≃* B) : e = f := by
  ext x
  rcases hB with hB | hB
  · letI : Subsingleton B := (Nat.card_eq_one_iff_unique.mp hB).1
    exact Subsingleton.elim _ _
  · by_cases hx : x = 1
    · simp [hx]
    · have hex : e x ≠ 1 := by
        intro he
        apply hx
        apply e.injective
        simpa using he
      have hfx : f x ≠ 1 := by
        intro hf
        apply hx
        apply f.injective
        simpa using hf
      obtain ⟨y, _hy, hy_unique⟩ :=
        (Nat.card_eq_two_iff' (1 : B)).mp hB
      exact (hy_unique (e x) hex).trans (hy_unique (f x) hfx).symm

/-- A norm-residue equivalence followed by the inclusion of its
decomposition subgroup into the global group. -/
def quotientEquivGlobal
    {U G : Type*} [CommGroup U] [Group G]
    (N : Subgroup U) (D : Subgroup G) (e : (U ⧸ N) ≃* D) : U →* G :=
  D.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' N))

/-- The preceding global map depends only on the norm subgroup and the
decomposition subgroup when the latter has order at most two. -/
theorem quotient_equiv_global
    {U G : Type*} [CommGroup U] [Group G]
    (N₁ N₂ : Subgroup U) (D₁ D₂ : Subgroup G)
    (e₁ : (U ⧸ N₁) ≃* D₁) (e₂ : (U ⧸ N₂) ≃* D₂)
    (hN : N₁ = N₂) (hD : D₁ = D₂)
    (hcard : Nat.card D₁ = 1 ∨ Nat.card D₁ = 2) :
    quotientEquivGlobal N₁ D₁ e₁ =
      quotientEquivGlobal N₂ D₂ e₂ := by
  subst N₂
  subst D₂
  rw [card_or_two hcard e₁ e₂]

/-- The canonical archimedean local Artin homomorphism, embedded in the
ambient global Galois group. -/
noncomputable def infiniteGlobalArtin
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L) v) :
    v.1.Completionˣ →* Gal(L/K) :=
  quotientEquivGlobal
    (infiniteCompletionNorm (K := K) (L := L) v w).range
    (absoluteValueDecomposition v.1 w.1.1)
    (infinitePlaceArtin v w)

set_option maxHeartbeats 3000000 in
-- Completion transport and norm-subgroup comparison require the dependent
-- archimedean algebra structures at both upper places.
set_option synthInstance.maxHeartbeats 500000 in
/-- Completed norm ranges at two infinite places above the same base place
are equal. -/
theorem infinite_place_range
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : InfinitePlace K)
    (z w : InfinitePlacesAbove (K := K) (L := L) v) :
    (infiniteCompletionNorm (K := K) (L := L) v z).range =
      (infiniteCompletionNorm (K := K) (L := L) v w).range := by
  letI := placesAboveAction (K := K) (L := L) v
  obtain ⟨sigma, hsigmaVal⟩ :=
    InfinitePlace.exists_smul_eq_of_comap_eq (z.2.trans w.2.symm)
  have hsigma : sigma • z = w := by
    apply Subtype.ext
    change infinitePlaceAction sigma z.1 = w.1
    apply Subtype.ext
    rw [infinite_action_val]
    exact congrArg (fun q : InfinitePlace L ↦ q.1) hsigmaVal
  have hz : sigma⁻¹ • w = z := by
    calc
      sigma⁻¹ • w = sigma⁻¹ • (sigma • z) :=
        congrArg (fun y => sigma⁻¹ • y) hsigma.symm
      _ = z := inv_smul_smul sigma z
  subst z
  letI : Algebra v.1.Completion (sigma⁻¹ • w).1.1.Completion :=
    (completionLies v.1 (sigma⁻¹ • w).1.1
      (infinite_lies_comap v
        (sigma⁻¹ • w).1 (sigma⁻¹ • w).2)).toAlgebra
  letI : Algebra v.1.Completion w.1.1.Completion :=
    (completionLies v.1 w.1.1
      (infinite_lies_comap v w.1 w.2)).toAlgebra
  letI : Module.Finite v.1.Completion (sigma⁻¹ • w).1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v (sigma⁻¹ • w)
  letI : Module.Finite v.1.Completion w.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v w
  let e : (sigma⁻¹ • w).1.1.Completion ≃ₐ[v.1.Completion]
      w.1.1.Completion :=
    { infiniteFamilyTransport v sigma w with
      commutes' := infinite_transport_base v sigma w }
  change normSubgroup v.1.Completion (sigma⁻¹ • w).1.1.Completion =
    normSubgroup v.1.Completion w.1.1.Completion
  exact norm_alg_equiv v.1.Completion _ _ e

/-- In an abelian extension, the decomposition groups of any two infinite
places above the same base place are equal. -/
theorem infinite_place_decomposition
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (v : InfinitePlace K)
    (w q : InfinitePlacesAbove (K := K) (L := L) v) :
    absoluteValueDecomposition v.1 w.1.1 =
      absoluteValueDecomposition v.1 q.1.1 := by
  obtain ⟨sigma, hsigma⟩ :=
    InfinitePlace.exists_smul_eq_of_comap_eq (w.2.trans q.2.symm)
  let wa : CompletionPlacesAbove (L := L) v.1 :=
    ⟨w.1.1, infinite_lies_comap v w.1 w.2⟩
  have hval : (sigma • wa).1 = q.1.1 := by
    change sigma • w.1.1 = q.1.1
    exact congrArg (fun z : InfinitePlace L ↦ z.1) hsigma
  rw [← hval]
  exact absolute_smul_commutative
    v.1 wa sigma

set_option maxHeartbeats 7000000 in
-- Both canonical archimedean norm-residue equivalences are elaborated before
-- the order-at-most-two uniqueness argument identifies them.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The canonical archimedean local Artin map is independent of the upper
infinite place. -/
theorem infinite_artin_independent
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (v : InfinitePlace K)
    (w q : InfinitePlacesAbove (K := K) (L := L) v) :
    infiniteGlobalArtin v w =
      infiniteGlobalArtin v q := by
  apply quotient_equiv_global
  · exact infinite_place_range v w q
  · exact infinite_place_decomposition v w q
  · let D := absoluteValueDecomposition v.1 w.1.1
    have hstabilizer : D = MulAction.stabilizer Gal(L/K) w.1 := by
      change absoluteValueDecomposition v.1 w.1.1 = _
      rw [absolute_decomposition_stabilizer]
      ext sigma
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
      constructor
      · intro h
        apply InfinitePlace.ext
        exact fun x ↦ DFunLike.congr_fun h x
      · intro h
        exact congrArg (fun z : InfinitePlace L ↦ z.1) h
    change Nat.card D = 1 ∨ Nat.card D = 2
    rw [hstabilizer]
    exact InfinitePlace.nat_card_stabilizer_eq_one_or_two K w.1

set_option maxHeartbeats 7000000 in
-- The completed norm quotient and the order-at-most-two uniqueness argument
-- elaborate in the same archimedean instance context.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Any map satisfying the archimedean local Artin predicate is the canonical
completed Artin map.  At infinity this follows from uniqueness of a group
equivalence when the decomposition group has order one or two. -/
theorem infinite_global_artin
    {K : Type u} [Field K] [NumberField K]
    (L : FASubext K)
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L.1) v)
    (phi : v.1.Completionˣ →* Gal(L.1/K))
    (hphi : InfiniteLayerArtin L v w phi) :
    letI : NumberField L.1 := NumberField.of_module_finite K L.1
    phi = infiniteGlobalArtin v w := by
  letI : NumberField L.1 := NumberField.of_module_finite K L.1
  rcases hphi with ⟨e, he⟩
  let N := (infiniteCompletionNorm (K := K) (L := L.1) v w).range
  let D := absoluteValueDecomposition v.1 w.1.1
  have hcard : Nat.card D = 1 ∨ Nat.card D = 2 := by
    have hstabilizer : D = MulAction.stabilizer Gal(L.1/K) w.1 := by
      change absoluteValueDecomposition v.1 w.1.1 = _
      rw [absolute_decomposition_stabilizer]
      ext sigma
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
      constructor
      · intro h
        apply InfinitePlace.ext
        exact fun x => DFunLike.congr_fun h x
      · intro h
        exact congrArg (fun z : InfinitePlace L.1 => z.1) h
    rw [hstabilizer]
    exact InfinitePlace.nat_card_stabilizer_eq_one_or_two K w.1
  have hquotient :
      quotientEquivGlobal N D e =
        quotientEquivGlobal N D
          (infinitePlaceArtin v w) :=
    quotient_equiv_global N N D D e
      (infinitePlaceArtin v w) rfl rfl hcard
  apply MonoidHom.ext
  intro x
  calc
    phi x = quotientEquivGlobal N D e x := he x
    _ = quotientEquivGlobal N D
          (infinitePlaceArtin v w) x :=
      DFunLike.congr_fun hquotient x
    _ = infiniteGlobalArtin v w x := rfl

/-- A homomorphism into a decomposition group, viewed as a homomorphism into
the ambient global Galois group. -/
def localArtinGlobal
    {U G X : Type*} [Group U] [Group G] [MulAction G X]
    (w : X) (φw : U →* MulAction.stabilizer G w) : U →* G :=
  (MulAction.stabilizer G w).subtype.comp φw

@[simp]
theorem local_artin_global
    {U G X : Type*} [Group U] [Group G] [MulAction G X]
    (w : X) (φw : U →* MulAction.stabilizer G w) (x : U) :
    localArtinGlobal w φw x = φw x :=
  rfl

/-- The precise local-reciprocity compatibility used in Milne's proof.

If `Q = σ • P`, the isomorphism of completions induced by `σ` identifies the
two local Artin maps by conjugation inside the global Galois group.  This is
the abstract ideal-stabilizer form of
`artin_conjugation_compatibility` proved above. -/
def ArtinConjugationCompatibility
    {U G X : Type*} [Group U] [Group G] [MulAction G X]
    (P Q : X)
    (φP : U →* MulAction.stabilizer G P)
    (φQ : U →* MulAction.stabilizer G Q) : Prop :=
  ∀ (σ : G), Q = σ • P →
    localArtinGlobal Q φQ =
      (MulAut.conj σ).toMonoidHom.comp (localArtinGlobal P φP)

/-- The decomposition group at a translated prime is the conjugate of the
original decomposition group. -/
theorem decomposition_smul_conjugate
    {G X : Type*} [Group G] [MulAction G X]
    (σ : G) (P : X) :
    MulAction.stabilizer G (σ • P) =
      (MulAction.stabilizer G P).map (MulAut.conj σ).toMonoidHom :=
  MulAction.stabilizer_smul_eq_stabilizer_map_conj σ P

/-- Conjugation by any element is trivial in a commutative group. -/
theorem conjugation_refl_commutative
    {G : Type*} [Group G] [IsMulCommutative G] (σ : G) :
    (MulAut.conj σ).toMonoidHom = MonoidHom.id G := by
  ext τ
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
  rw [mul_comm σ τ, mul_inv_cancel_right]

/-- **Lemma V.5.1 at finite completions.**  The decomposition group and the
canonical finite local Artin map, transported along the completion
isomorphism induced by `sigma`, are independent of the chosen place above
the finite prime `P`.  No local Artin map is supplied as a hypothesis. -/
theorem finitePlaceCompletion
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val)
    (sigma : Gal(L/K)) :
    absoluteValueDecomposition (FinitePlace.mk P).val w.1 =
        absoluteValueDecomposition (FinitePlace.mk P).val
          (sigma • w).1 ∧
      conjugateGlobalArtin P w sigma =
        globalArtinHom P w :=
  ⟨absolute_smul_commutative
      (FinitePlace.mk P).val w sigma,
    artin_independent_conjugate P w sigma⟩

/-- Every second completion above `P` is conjugate to the first, so the
input-free completion theorem applies to arbitrary choices of upper place. -/
theorem place_completion_places
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w q : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    ∃ sigma : Gal(L/K), q = sigma • w ∧
      absoluteValueDecomposition (FinitePlace.mk P).val w.1 =
        absoluteValueDecomposition (FinitePlace.mk P).val q.1 ∧
      conjugateGlobalArtin P w sigma =
        globalArtinHom P w := by
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  obtain ⟨sigma, hsigma⟩ := MulAction.exists_smul_eq Gal(L/K) w q
  refine ⟨sigma, hsigma.symm, ?_,
    artin_independent_conjugate P w sigma⟩
  rw [← hsigma]
  exact absolute_smul_commutative
    v w sigma

/-- **Lemma V.5.1 at infinite completions.**  Both the archimedean
decomposition group and the constructed norm-residue map are independent of
the upper infinite place. -/
theorem infinitePlaceCompletion
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)]
    (v : InfinitePlace K)
    (w q : InfinitePlacesAbove (K := K) (L := L) v) :
    absoluteValueDecomposition v.1 w.1.1 =
        absoluteValueDecomposition v.1 q.1.1 ∧
      infiniteGlobalArtin v w =
        infiniteGlobalArtin v q :=
  ⟨infinite_place_decomposition v w q,
    infinite_artin_independent v w q⟩

set_option maxHeartbeats 7000000 in
-- Expanding the completed norm-residue map requires the full local-field
-- and completed-Galois instance stack.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The canonical completed finite map is a finite-layer local Artin map in
the precise norm-residue sense used by Proposition V.5.2. -/
theorem adic_global_artin
    {K : Type} [Field K] [NumberField K]
    (L : FASubext K) [NumberField L.1]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L.1) P)
    (hnormalized :
      let w := (placesAboveFactors
        (K := K) (L := L.1) P).symm Q
      ∀ q : CompletionPlacesAbove (L := L.1) (FinitePlace.mk P).val,
        adicGlobalArtin P w =
          adicArtinUniverse K L.1 P q) :
    let w := (placesAboveFactors
      (K := K) (L := L.1) P).symm Q
    LayerLocalArtin L P Q
      (adicGlobalArtin P w) := by
  let w := (placesAboveFactors
    (K := K) (L := L.1) P).symm Q
  let v := (FinitePlace.mk P).val
  have hwq : w.1.IsEquiv
      (FinitePlace.mk (upperPrime (K := K) (L := L.1) P Q)).val := by
    exact
      (Towers.CField.NIndex.primeCompletionModel
        K L.1 P Q).isEquiv_upper
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : Finite
      (CompletionPlacesAbove (L := L.1) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := L.1) v) :=
    absolute_value_extension (K := K) (L := L.1) v
  letI : MulAction.IsPretransitive Gal(L.1/K)
      (CompletionPlacesAbove (L := L.1) v) :=
    completion_above_pretransitive P
  letI : FiniteDimensional v.Completion w.1.Completion :=
    placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let decomp := decompositionCompletionExtension v w.1
  letI : IsMulCommutative Gal(w.1.Completion/v.Completion) := by
    refine ⟨⟨fun sigma tau ↦ ?_⟩⟩
    apply decomp.symm.injective
    simpa only [map_mul] using mul_comm (decomp.symm sigma) (decomp.symm tau)
  refine ⟨w.1, w.2, hwq,
    abelianLocalArtin v.Completion w.1.Completion, ?_, ?_⟩
  · intro x
    simp only [adicGlobalArtin, MonoidHom.comp_apply]
    have hcompletion : globalArtinHom P w =
        completionArtinGlobal v w
          ((abelianLocalArtin
            v.Completion w.1.Completion).toMonoidHom.comp
              (QuotientGroup.mk' (normSubgroup
                v.Completion w.1.Completion))) := by
      rfl
    rw [hcompletion]
    rfl
  · exact hnormalized

set_option maxHeartbeats 7000000 in
-- Expanding the finite abelian subextension installs the number-field and
-- completed Galois structures used by the archimedean equivalence.
set_option synthInstance.maxHeartbeats 1000000 in
/-- The constructed archimedean homomorphism is an infinite-layer local
Artin map in the sense used by the Chapter V global Artin statement. -/
theorem infinite_artin_local
    {K : Type u} [Field K] [NumberField K]
    (L : FASubext K)
    (v : InfinitePlace K)
    (w : InfinitePlacesAbove (K := K) (L := L.1) v) :
    letI : NumberField L.1 := NumberField.of_module_finite K L.1
    InfiniteLayerArtin L v w
      (infiniteGlobalArtin v w) := by
  letI : NumberField L.1 := NumberField.of_module_finite K L.1
  refine ⟨infinitePlaceArtin v w, ?_⟩
  intro x
  rfl

/-- **Lemma V.5.1, completion-level Artin-map clause.**  In an abelian
extension, a local map and its transport to any conjugate completed place
have the same value in the global Galois group. -/
theorem completion_independent_conjugate
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Normal K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : CompletionPlacesAbove (L := L) v) (sigma : Gal(L/K))
    (phi :
      letI : Algebra v.Completion w.1.Completion :=
        (completionLies v w.1 w.2).toAlgebra
      v.Completionˣ →* Gal(w.1.Completion/v.Completion)) :
    completionArtinGlobal v (sigma • w)
        (conjugateCompletionArtin v w sigma phi) =
      completionArtinGlobal v w phi := by
  rw [artin_conjugation_compatibility,
    conjugation_refl_commutative]
  rfl

/-- The two assertions of Lemma V.5.1 for an actual pair of conjugate
completion places: equality of decomposition groups and independence of the
transported local Artin homomorphism. -/
theorem completion
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [Normal K L] [FiniteDimensional K L] [IsMulCommutative Gal(L/K)]
    (v : AbsoluteValue K ℝ) [Fact v.IsNontrivial]
    [IsUltrametricDist v.Completion]
    (w : CompletionPlacesAbove (L := L) v) (sigma : Gal(L/K))
    (phi :
      letI : Algebra v.Completion w.1.Completion :=
        (completionLies v w.1 w.2).toAlgebra
      v.Completionˣ →* Gal(w.1.Completion/v.Completion)) :
    absoluteValueDecomposition v w.1 =
        absoluteValueDecomposition v (sigma • w).1 ∧
      completionArtinGlobal v (sigma • w)
          (conjugateCompletionArtin v w sigma phi) =
        completionArtinGlobal v w phi :=
  ⟨absolute_smul_commutative v w sigma,
    completion_independent_conjugate v w sigma phi⟩

/-- In an abelian Galois group, decomposition groups at two primes over the
same base prime are equal.  This proves the first clause of Lemma V.5.1
directly from prime transitivity and the stabilizer-conjugation formula. -/
theorem decomposition_lies_source
    {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [IsMulCommutative G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B]
    (p : Ideal A) (P Q : Ideal B)
    [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p] :
    MulAction.stabilizer G P = MulAction.stabilizer G Q := by
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup p P Q G
  rw [← hσ, decomposition_smul_conjugate]
  rw [conjugation_refl_commutative]
  exact (MulAction.stabilizer G P).map_id.symm

/-- Abstract ideal-stabilizer consequence of a supplied conjugation square.
This remains useful independently of number fields, but is not the source
endpoint for Lemma V.5.1. -/
theorem abstract_conjugation_compatibility
    {A B G U : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [IsMulCommutative G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] [Group U]
    (p : Ideal A) (P Q : Ideal B)
    [P.IsPrime] [P.LiesOver p] [Q.IsPrime] [Q.LiesOver p]
    (φP : U →* MulAction.stabilizer G P)
    (φQ : U →* MulAction.stabilizer G Q)
    (hcompat : ArtinConjugationCompatibility P Q φP φQ) :
    ∃ hD : MulAction.stabilizer G P = MulAction.stabilizer G Q,
    (MulEquiv.subgroupCongr hD).toMonoidHom.comp φP = φQ
  := by
  obtain ⟨σ, hσ⟩ :=
    Ideal.exists_smul_eq_of_isGaloisGroup p P Q G
  have hD : MulAction.stabilizer G P = MulAction.stabilizer G Q :=
    decomposition_lies_source p P Q
  refine ⟨hD, ?_⟩
  have hglobal : localArtinGlobal Q φQ =
      localArtinGlobal P φP := by
    rw [hcompat σ hσ.symm]
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      local_artin_global, MulAut.conj_apply]
    rw [mul_comm σ (φP x : G), mul_inv_cancel_right]
  ext x
  have hx := DFunLike.congr_fun hglobal x
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_apply, local_artin_global] using hx.symm

/-- The finite-place half of the actual Lemma V.5.1 source statement.  The
local map is the Theorem III.3.1 norm-residue map constructed above, and its
map at the second completion is its transport along the exhibited Galois
conjugation. -/
def GlobalArtinCompatibility
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] : Prop :=
  ∀ (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
      (w q : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val),
    ∃ sigma : Gal(L/K), q = sigma • w ∧
      absoluteValueDecomposition (FinitePlace.mk P).val w.1 =
        absoluteValueDecomposition (FinitePlace.mk P).val q.1 ∧
      conjugateGlobalArtin P w sigma =
        globalArtinHom P w

/-- The infinite-place half of the actual Lemma V.5.1 source statement.  Its
norm-residue maps are constructed from the archimedean norm quotients, so no
local map or compatibility square is supplied as an input. -/
def InfiniteArtinCompatibility
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] : Prop :=
  ∀ (v : InfinitePlace K)
      (w q : InfinitePlacesAbove (K := K) (L := L) v),
    absoluteValueDecomposition v.1 w.1.1 =
        absoluteValueDecomposition v.1 q.1.1 ∧
      infiniteGlobalArtin v w =
        infiniteGlobalArtin v q

/-- Lemma V.5.1 with its finite and infinite local maps assembled.  In
particular, this endpoint has no `ArtinConjugationCompatibility`
hypothesis. -/
theorem globalArtinStatement
    {K L : Type} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] :
    (GlobalArtinCompatibility (K := K) (L := L) ∧
          InfiniteArtinCompatibility (K := K) (L := L)) := by
  constructor
  · exact fun P w q ↦ place_completion_places P w q
  · exact fun v w q ↦ infinitePlaceCompletion v w q

end

end Towers.CField.Recip

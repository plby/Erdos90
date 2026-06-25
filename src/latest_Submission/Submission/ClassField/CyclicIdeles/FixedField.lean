import Submission.NumberTheory.Galois.CompositumSplittingPrimes
import Submission.ClassField.NormIndex.CanonicalTateFormula
import Submission.ClassField.CyclicIdeles.ClassRestrictionComparison
import Submission.ClassField.CyclicIdeles.NormalSubgroupBridge

/-!
# Chapter VII, Section 5, Lemma 5.4: the fixed-field comparison

For a normal subgroup `H ≤ Gal(L/K)`, the canonical extension of idèle
classes identifies `C_(L^H)` with the `H`-invariants of `C_L`.  The
identification is equivariant for the standard isomorphism
`Gal(L/K) / H ≃ Gal(L^H/K)`.  This supplies the two quotient-side and two
restriction-side comparisons used in the inflation--restriction induction.
-/

namespace Submission.CField.CIdeles

open CategoryTheory Limits
open IsDedekindDomain NumberField Representation
open Submission.NumberTheory.Milne
open Submission.CField.Shifting
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex
open Submission.CField.HNorm

open scoped Pointwise

noncomputable section

universe u

private abbrev OK (F : Type u) [Field F] [NumberField F] :=
  NumberField.RingOfIntegers F

private theorem cast_continuous_fixed
    {F : Type u} [Field F] [NumberField F]
    {P P' : HeightOneSpectrum (OK F)} (h : P = P') :
    Continuous (RingEquiv.cast
      (R := fun V : HeightOneSpectrum (OK F) ↦ V.adicCompletion F) h) := by
  subst P'
  exact continuous_id

private theorem cast_embedding_fixed
    {F : Type u} [Field F] [NumberField F]
    {P P' : HeightOneSpectrum (OK F)} (h : P = P') (x : F) :
    RingEquiv.cast
        (R := fun V : HeightOneSpectrum (OK F) ↦ V.adicCompletion F) h
        (FinitePlace.embedding P x) =
      FinitePlace.embedding P' x := by
  subst P'
  rfl

private theorem cast_dependent_fixed
    {F : Type u} [Field F] [NumberField F]
    {P P' : HeightOneSpectrum (OK F)} (h : P = P')
    (x : (V : HeightOneSpectrum (OK F)) → V.adicCompletion F) :
    RingEquiv.cast
        (R := fun V : HeightOneSpectrum (OK F) ↦ V.adicCompletion F) h
        (x P) = x P' := by
  subst P'
  rfl

private theorem prime_smul_restrict
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : Type u) [Field E] [NumberField E]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L]
    (sigma : Gal(L/K)) (Q : HeightOneSpectrum (OK L)) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := finitePrimeAction (K := K) (L := E)
    (sigma • Q).under (OK E) =
      (AlgEquiv.restrictNormalHom E sigma) • (Q.under (OK E)) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := finitePrimeAction (K := K) (L := E)
  apply HeightOneSpectrum.ext
  change Ideal.under (OK E) (sigma • Q).asIdeal =
    ((AlgEquiv.restrictNormalHom E sigma) • (Q.under (OK E))).asIdeal
  rw [prime_action_ideal, prime_action_ideal]
  exact smul_restrict sigma Q.asIdeal

set_option maxHeartbeats 3000000 in
-- Finite-idèle extension across the fixed field unfolds dependent prime coordinates.
set_option synthInstance.maxHeartbeats 200000 in
set_option maxRecDepth 100000 in
private theorem extension_restrict_smul
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : Type u) [Field E] [NumberField E]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L]
    (sigma : Gal(L/K))
    (x : FiniteIdeles (OK E) E) :
    letI := finitePrimeAction (K := K) (L := L)
    letI := finitePrimeAction (K := K) (L := E)
    letI := finiteIdelesAction (K := K) (L := L)
    letI := finiteIdelesAction (K := K) (L := E)
    sigma • ideleMonoidHom (K := E) (L := L) x =
      ideleMonoidHom (K := E) (L := L)
        ((AlgEquiv.restrictNormalHom E sigma) • x) := by
  letI := finitePrimeAction (K := K) (L := L)
  letI := finitePrimeAction (K := K) (L := E)
  letI := finiteIdelesAction (K := K) (L := L)
  letI := finiteIdelesAction (K := K) (L := E)
  apply RestrictedProduct.ext
  intro Q
  change (sigma • ideleMonoidHom
      (K := E) (L := L) x).1 Q =
    (ideleMonoidHom (K := E) (L := L)
      ((AlgEquiv.restrictNormalHom E sigma) • x)).1 Q
  rw [ideles_action_coordinate]
  let tau : Gal(E/K) := AlgEquiv.restrictNormalHom E sigma
  let Psource := (sigma⁻¹ • Q).under (OK E)
  let Ptarget := Q.under (OK E)
  let Paction := tau⁻¹ • Ptarget
  have hUnder : Psource = Paction := by
    dsimp only [Psource, Paction, tau, Ptarget]
    rw [prime_smul_restrict (E := E)]
    rw [map_inv]
  let castBase : Psource.adicCompletion E →+* Paction.adicCompletion E :=
    (RingEquiv.cast
      (R := fun V : HeightOneSpectrum (OK E) ↦ V.adicCompletion E)
      hUnder).toRingHom
  have hhom :
      (finitePlaceTransport (K := K) sigma Q).toRingHom.comp
          (coordinateExtensionHom
            (K := E) (L := L) (sigma⁻¹ • Q)) =
        ((coordinateExtensionHom (K := E) (L := L) Q).comp
          (finitePlaceTransport (K := K) tau Ptarget).toRingHom).comp
            castBase := by
    apply DFunLike.ext _ _
    intro z
    exact congrFun
      ((Psource.denseRange_algebraMap E).equalizer
        ((finite_transport_continuous (K := K) sigma Q).comp
          (extension_ring_continuous
            (K := E) (L := L) (sigma⁻¹ • Q)))
        (((extension_ring_continuous
            (K := E) (L := L) Q).comp
          (finite_transport_continuous (K := K) tau Ptarget)).comp
            (cast_continuous_fixed hUnder))
        (funext fun a ↦ by
          change finitePlaceTransport (K := K) sigma Q
              (coordinateExtensionHom
                (K := E) (L := L) (sigma⁻¹ • Q)
                (FinitePlace.embedding Psource a)) =
            coordinateExtensionHom (K := E) (L := L) Q
              (finitePlaceTransport (K := K) tau Ptarget
                (RingEquiv.cast hUnder (FinitePlace.embedding Psource a)))
          have hsource := extension_comp_embedding
            (K := E) (L := L) (sigma⁻¹ • Q) a
          change coordinateExtensionHom
              (K := E) (L := L) (sigma⁻¹ • Q)
                (FinitePlace.embedding Psource a) =
            FinitePlace.embedding (sigma⁻¹ • Q) (algebraMap E L a)
              at hsource
          rw [hsource, place_transport_embedding]
          rw [cast_embedding_fixed]
          rw [place_transport_embedding]
          have htarget := extension_comp_embedding
            (K := E) (L := L) Q (tau a)
          change coordinateExtensionHom
              (K := E) (L := L) Q
                (FinitePlace.embedding Ptarget (tau a)) =
            FinitePlace.embedding Q (algebraMap E L (tau a)) at htarget
          rw [htarget]
          exact congrArg (FinitePlace.embedding Q)
            (AlgEquiv.restrictNormal_commutes sigma E a).symm)) z
  apply Units.ext
  change finitePlaceTransport (K := K) sigma Q
      (extensionMonoidHom
        (K := E) (L := L) (sigma⁻¹ • Q) (x.1 Psource) :
          (sigma⁻¹ • Q).adicCompletion L) =
    (extensionMonoidHom (K := E) (L := L) Q
      (Units.map
        (finitePlaceTransport (K := K) tau Ptarget).toRingHom.toMonoidHom
        (x.1 Paction)) : Q.adicCompletion L)
  rw [extension_monoid_val,
    extension_monoid_val]
  calc
    finitePlaceTransport (K := K) sigma Q
        (coordinateExtensionHom
          (K := E) (L := L) (sigma⁻¹ • Q)
          (x.1 Psource : Psource.adicCompletion E)) =
      coordinateExtensionHom (K := E) (L := L) Q
        (finitePlaceTransport (K := K) tau Ptarget
          (RingEquiv.cast hUnder
            (x.1 Psource : Psource.adicCompletion E))) :=
      RingHom.congr_fun hhom (x.1 Psource : Psource.adicCompletion E)
    _ = coordinateExtensionHom (K := E) (L := L) Q
        (finitePlaceTransport (K := K) tau Ptarget
          (x.1 Paction : Paction.adicCompletion E)) := by
      have hcast : RingEquiv.cast hUnder
          (x.1 Psource : Psource.adicCompletion E) =
          (x.1 Paction : Paction.adicCompletion E) :=
        cast_dependent_fixed hUnder
          (fun V ↦ (x.1 V : V.adicCompletion E))
      rw [hcast]

private theorem smul_comap_restrict
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : Type u) [Field E] [NumberField E]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L]
    (sigma : Gal(L/K)) (w : InfinitePlace L) :
    (sigma⁻¹ • w).comap (algebraMap E L) =
      (AlgEquiv.restrictNormalHom E sigma)⁻¹ •
        (w.comap (algebraMap E L)) := by
  rw [InfinitePlace.comap_smul]
  change w.comap ((sigma⁻¹).symm.toRingEquiv.toRingHom.comp
      (algebraMap E L)) =
    (w.comap (algebraMap E L)).comap
      ((AlgEquiv.restrictNormalHom E sigma)⁻¹).symm.toRingEquiv.toRingHom
  rw [← InfinitePlace.comap_comp]
  apply congrArg (fun f : E →+* L ↦ w.comap f)
  ext a
  exact (AlgEquiv.restrictNormal_commutes sigma E a).symm

private theorem infinite_cast_continuous
    {F : Type u} [Field F] [NumberField F]
    {v v' : InfinitePlace F} (h : v = v') :
    Continuous (RingEquiv.cast
      (R := fun z : InfinitePlace F ↦ z.1.Completion) h) := by
  subst v'
  exact continuous_id

private theorem infinite_cast_embedding
    {F : Type u} [Field F] [NumberField F]
    {v v' : InfinitePlace F} (h : v = v') (x : F) :
    RingEquiv.cast (R := fun z : InfinitePlace F ↦ z.1.Completion) h
        (completionEmbedding v.1 x) = completionEmbedding v'.1 x := by
  subst v'
  rfl

private theorem infinite_cast_dependent
    {F : Type u} [Field F] [NumberField F]
    {v v' : InfinitePlace F} (h : v = v')
    (x : (z : InfinitePlace F) → z.1.Completion) :
    RingEquiv.cast (R := fun z : InfinitePlace F ↦ z.1.Completion) h
        (x v) = x v' := by
  subst v'
  rfl

set_option maxHeartbeats 3000000 in
-- Infinite-idèle extension across the fixed field unfolds dependent completion fibers.
set_option maxRecDepth 100000 in
private theorem monoid_restrict_smul
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : Type u) [Field E] [NumberField E]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L]
    (sigma : Gal(L/K)) (x : (InfiniteAdeleRing E)ˣ) :
    letI := infiniteIdelesAction (K := K) (L := L)
    letI := infiniteIdelesAction (K := K) (L := E)
    sigma • infiniteMonoidHom (K := E) (L := L) x =
      infiniteMonoidHom (K := E) (L := L)
        ((AlgEquiv.restrictNormalHom E sigma) • x) := by
  letI := infiniteIdelesAction (K := K) (L := L)
  letI := infiniteIdelesAction (K := K) (L := E)
  apply Units.ext
  funext w
  let tau : Gal(E/K) := AlgEquiv.restrictNormalHom E sigma
  let vsource := (sigma⁻¹ • w).comap (algebraMap E L)
  let vtarget := w.comap (algebraMap E L)
  let vaction := tau⁻¹ • vtarget
  have hComap : vsource = vaction := by
    exact smul_comap_restrict E sigma w
  let sourceLies := infinite_lies_comap
    vsource (sigma⁻¹ • w) rfl
  let targetLies := infinite_lies_comap
    vtarget w rfl
  let castBase : vsource.1.Completion →+* vaction.1.Completion :=
    (RingEquiv.cast
      (R := fun z : InfinitePlace E ↦ z.1.Completion) hComap).toRingHom
  have hhom :
      (numberInfiniteTransport (K := K) sigma w).toRingHom.comp
          (completionLies vsource.1 (sigma⁻¹ • w).1 sourceLies) =
        ((completionLies vtarget.1 w.1 targetLies).comp
          (numberInfiniteTransport (K := K) tau vtarget).toRingHom).comp
            castBase := by
    apply DFunLike.ext _ _
    intro z
    exact congrFun
      ((dense_range_embedding vsource.1).equalizer
        ((number_transport_continuous
            (K := K) sigma w).comp
          (completion_lies_isometry
            vsource.1 (sigma⁻¹ • w).1 sourceLies).continuous)
        (((completion_lies_isometry
            vtarget.1 w.1 targetLies).continuous.comp
          (number_transport_continuous
            (K := K) tau vtarget)).comp
              (infinite_cast_continuous hComap))
        (funext fun a ↦ by
          change numberInfiniteTransport (K := K) sigma w
              (completionLies vsource.1 (sigma⁻¹ • w).1 sourceLies
                (completionEmbedding vsource.1 a)) =
            completionLies vtarget.1 w.1 targetLies
              (numberInfiniteTransport (K := K) tau vtarget
                (RingEquiv.cast hComap (completionEmbedding vsource.1 a)))
          have hsource := RingHom.congr_fun
            (completion_lies_comp
              vsource.1 (sigma⁻¹ • w).1 sourceLies) a
          change completionLies vsource.1 (sigma⁻¹ • w).1 sourceLies
              (completionEmbedding vsource.1 a) =
            completionEmbedding (sigma⁻¹ • w).1 (algebraMap E L a) at hsource
          rw [hsource]
          rw [number_transport_embedding]
          rw [infinite_cast_embedding]
          rw [number_transport_embedding]
          have htarget := RingHom.congr_fun
            (completion_lies_comp vtarget.1 w.1 targetLies) (tau a)
          change completionLies vtarget.1 w.1 targetLies
              (completionEmbedding vtarget.1 (tau a)) =
            completionEmbedding w.1 (algebraMap E L (tau a)) at htarget
          rw [htarget]
          exact congrArg (completionEmbedding w.1)
            (AlgEquiv.restrictNormal_commutes sigma E a).symm)) z
  change numberInfiniteTransport (K := K) sigma w
      (completionLies vsource.1 (sigma⁻¹ • w).1 sourceLies
        ((MulEquiv.piUnits x vsource : _) : _)) =
    completionLies vtarget.1 w.1 targetLies
      (numberInfiniteTransport (K := K) tau vtarget
        ((MulEquiv.piUnits x vaction : _) : _))
  calc
    numberInfiniteTransport (K := K) sigma w
        (completionLies vsource.1 (sigma⁻¹ • w).1 sourceLies
          ((MulEquiv.piUnits x vsource : _) : _)) =
      completionLies vtarget.1 w.1 targetLies
        (numberInfiniteTransport (K := K) tau vtarget
          (RingEquiv.cast hComap ((MulEquiv.piUnits x vsource : _) : _))) :=
      RingHom.congr_fun hhom ((MulEquiv.piUnits x vsource : _) : _)
    _ = completionLies vtarget.1 w.1 targetLies
        (numberInfiniteTransport (K := K) tau vtarget
          ((MulEquiv.piUnits x vaction : _) : _)) := by
      have hcast : RingEquiv.cast hComap
          ((MulEquiv.piUnits x vsource : _) : vsource.1.Completion) =
          ((MulEquiv.piUnits x vaction : _) : vaction.1.Completion) :=
        infinite_cast_dependent hComap
          (fun v ↦ ((MulEquiv.piUnits x v : _) : v.1.Completion))
      rw [hcast]

set_option maxHeartbeats 3000000 in
-- Combining finite and infinite restriction transport is elaboration-heavy.
set_option maxRecDepth 100000 in
/-- Extension of idèles from a normal intermediate field commutes with an
ambient Galois automorphism and its restriction to that field. -/
theorem idele_restrict_smul
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : Type u) [Field E] [NumberField E]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L]
    (sigma : Gal(L/K)) (x : IdeleGroup (OK E) E) :
    (idelesGaloisAction (K := K) (L := L)).smul sigma
        (ideleExtensionMonoid (K := E) (L := L) x) =
      ideleExtensionMonoid (K := E) (L := L)
        ((idelesGaloisAction (K := K) (L := E)).smul
          (AlgEquiv.restrictNormalHom E sigma) x) := by
  apply Prod.ext
  · exact monoid_restrict_smul E sigma x.1
  · exact extension_restrict_smul E sigma x.2

theorem canonical_restrict_smul
    {K L : Type u} [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (E : Type u) [Field E] [NumberField E]
    [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [FiniteDimensional K E] [FiniteDimensional E L]
    [IsGalois K E] [IsGalois E L]
    (sigma : Gal(L/K))
    (c : IdeleClassGroup (OK E) E) :
    let D := canonicalExtensionData (K := E) (L := L)
    letI := ideleDistribAction (K := K) (L := L)
    letI := ideleDistribAction (K := K) (L := E)
    D.classMap ((AlgEquiv.restrictNormalHom E sigma) • c) =
      sigma • D.classMap c := by
  let D := canonicalExtensionData (K := E) (L := L)
  letI := ideleDistribAction (K := K) (L := L)
  letI := ideleDistribAction (K := K) (L := E)
  change D.classMap ((AlgEquiv.restrictNormalHom E sigma) • c) =
    sigma • D.classMap c
  induction c using Quotient.inductionOn' with
  | _ x =>
      change QuotientGroup.mk' (principalIdeles (OK L) L)
          (ideleExtensionMonoid (K := E) (L := L)
            ((idelesGaloisAction (K := K) (L := E)).smul
              (AlgEquiv.restrictNormalHom E sigma) x)) =
        QuotientGroup.mk' (principalIdeles (OK L) L)
          ((idelesGaloisAction (K := K) (L := L)).smul sigma
            (ideleExtensionMonoid (K := E) (L := L) x))
      exact congrArg (QuotientGroup.mk' (principalIdeles (OK L) L))
        (idele_restrict_smul E sigma x).symm

set_option maxHeartbeats 3000000 in
-- Constructing the fixed-field quotient map unfolds nested idèle-class quotients.
set_option maxRecDepth 100000 in
private noncomputable def fixedFieldInvariants
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal]
    (c : Additive (IdeleClassGroup (OK (IntermediateField.fixedField H))
      (IntermediateField.fixedField H))) :
    (explicitIdeleRepresentation (K := K) (L := L)).quotientToInvariants H := by
  let E := IntermediateField.fixedField H
  let D := canonicalExtensionData (K := E) (L := L)
  let eH := IntermediateField.subgroupEquivAlgEquiv H
  refine ⟨Additive.ofMul (D.classMap c.toMul), ?_⟩
  intro h
  apply Additive.toMul.injective
  change (ideleDistribAction (K := E) (L := L)).smul
      (eH h) (D.classMap c.toMul) = D.classMap c.toMul
  have hfixed := (D.class_map_fixed c.toMul).2 (eH h)
  exact hfixed

set_option maxHeartbeats 1000000 in
-- Packaging the quotient map as a homomorphism retains dependent quotient witnesses.
set_option maxRecDepth 100000 in
private noncomputable def fixedInvariantsHom
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal] :
    Additive (IdeleClassGroup (OK (IntermediateField.fixedField H))
        (IntermediateField.fixedField H)) →+
      (explicitIdeleRepresentation (K := K) (L := L)).quotientToInvariants H where
  toFun := fixedFieldInvariants K L H
  map_zero' := by
    apply Subtype.ext
    apply Additive.toMul.injective
    exact map_one (canonicalExtensionData
      (K := IntermediateField.fixedField H) (L := L)).classMap
  map_add' a b := by
    apply Subtype.ext
    apply Additive.toMul.injective
    exact map_mul (canonicalExtensionData
      (K := IntermediateField.fixedField H) (L := L)).classMap a.toMul b.toMul

set_option maxHeartbeats 3000000 in
-- Bijectivity expands the fixed-field descent and both quotient presentations.
set_option maxRecDepth 100000 in
private theorem fixed_invariants_bijective
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal] :
    Function.Bijective
      (fixedInvariantsHom K L H) := by
  let E := IntermediateField.fixedField H
  let D := canonicalExtensionData (K := E) (L := L)
  let eH := IntermediateField.subgroupEquivAlgEquiv H
  have hbij : Function.Bijective D.class_map_fixed :=
    canonical_fixed_bijective
      (K := E) (L := L)
  constructor
  · intro a b hab
    apply Additive.toMul.injective
    apply hbij.1
    apply Subtype.ext
    exact congrArg (fun z ↦ z.1.toMul) hab
  · intro x
    let cfixed : fixedIdeleClasses (K := E) (L := L) :=
      ⟨x.1.toMul, by
        intro tau
        let h : H := eH.symm tau
        have hx := congrArg Additive.toMul (x.2 h)
        change (ideleDistribAction (K := E) (L := L)).smul
            (eH h) x.1.toMul = x.1.toMul at hx
        rw [eH.apply_symm_apply] at hx
        exact hx⟩
    obtain ⟨c, hc⟩ := hbij.2 cfixed
    refine ⟨Additive.ofMul c, ?_⟩
    apply Subtype.ext
    apply Additive.toMul.injective
    have hcval : D.classMap c = cfixed.1 := congrArg Subtype.val hc
    change D.classMap c = x.1.toMul
    exact hcval

private noncomputable def fixedIdeleInvariants
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal] :
    Additive (IdeleClassGroup (OK (IntermediateField.fixedField H))
        (IntermediateField.fixedField H)) ≃+
      (explicitIdeleRepresentation (K := K) (L := L)).quotientToInvariants H :=
  AddEquiv.ofBijective
    (fixedInvariantsHom K L H)
    (fixed_invariants_bijective K L H)

private theorem fixed_idele_invariants
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal]
    (c : Additive (IdeleClassGroup (OK (IntermediateField.fixedField H))
      (IntermediateField.fixedField H))) :
    fixedIdeleInvariants K L H c =
      fixedInvariantsHom K L H c := rfl

set_option maxHeartbeats 1000000 in
-- Equivariance of the additive equivalence unfolds the transported quotient action.
private theorem fixed_invariants_equivariant
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal]
    (g : Gal(L/K) ⧸ H)
    (c : Additive (IdeleClassGroup (OK (IntermediateField.fixedField H))
      (IntermediateField.fixedField H))) :
    fixedIdeleInvariants K L H
        ((explicitIdeleRepresentation
          (K := K) (L := IntermediateField.fixedField H)).ρ
            (IsGalois.normalAutEquivQuotient H g) c) =
      ((explicitIdeleRepresentation (K := K) (L := L)).quotientToInvariants H).ρ
        g (fixedIdeleInvariants K L H c) := by
  induction g using QuotientGroup.induction_on with
  | _ sigma =>
      apply Subtype.ext
      apply Additive.toMul.injective
      rw [fixed_idele_invariants,
        fixed_idele_invariants]
      change (canonicalExtensionData
          (K := IntermediateField.fixedField H) (L := L)).classMap
            ((ideleDistribAction
              (K := K) (L := IntermediateField.fixedField H)).smul
                (AlgEquiv.restrictNormalHom
                  (IntermediateField.fixedField H) sigma) c.toMul) =
        (ideleDistribAction (K := K) (L := L)).smul sigma
          ((canonicalExtensionData
            (K := IntermediateField.fixedField H) (L := L)).classMap c.toMul)
      exact canonical_restrict_smul
        (IntermediateField.fixedField H) sigma c.toMul

/-- At the integral explicit-idèle-class level, the quotient action on
`H`-invariants is the action on the idèle classes of the fixed field. -/
private noncomputable def explicitFixedIso
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal] :
    (explicitIdeleRepresentation (K := K) (L := L)).quotientToInvariants H ≅
      Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
        (explicitIdeleRepresentation
          (K := K) (L := IntermediateField.fixedField H)) := by
  symm
  apply Rep.mkIso
  refine Representation.Equiv.mk
    (fixedIdeleInvariants K L H).toIntLinearEquiv ?_
  intro g
  apply LinearMap.ext
  intro c
  exact fixed_invariants_equivariant
    K L H g c

private noncomputable def integralFixedIso
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal] :
    (classCokernelRepresentation (K := K) (L := L)).quotientToInvariants H ≅
      Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
        (classCokernelRepresentation
          (K := K) (L := IntermediateField.fixedField H)) :=
  ((Rep.quotientToInvariantsFunctor ℤ H).mapIso
      (cokernelIsoExplicit (K := K) (L := L))) ≪≫
    explicitFixedIso K L H ≪≫
    ((Rep.resFunctor (IsGalois.normalAutEquivQuotient H).toMonoidHom).mapIso
      (cokernelIsoExplicit
        (K := K) (L := IntermediateField.fixedField H))).symm

private noncomputable def uliftInvariantsIso
    {G : Type u} [Group G] (A : Rep.{u, 0, u} ℤ G)
    (H : Subgroup G) [H.Normal] :
    (uliftIntegralRepresentation A).quotientToInvariants H ≅
      uliftIntegralRepresentation (A.quotientToInvariants H) := by
  apply Rep.mkIso
  refine
    { toLinearEquiv :=
        { toFun := fun x ↦ ⟨x.1, x.2⟩
          invFun := fun x ↦ ⟨x.1, x.2⟩
          left_inv := fun x ↦ by apply Subtype.ext; rfl
          right_inv := fun x ↦ by apply Subtype.ext; rfl
          map_add' := fun x y ↦ by apply Subtype.ext; rfl
          map_smul' := fun r x ↦ by apply Subtype.ext; rfl }
      isIntertwining' := fun g ↦ by
        apply LinearMap.ext
        intro x
        apply Subtype.ext
        induction g using QuotientGroup.induction_on with
        | _ g => rfl }

private noncomputable def uliftResIso
    {G Q : Type u} [Group G] [Group Q]
    (f : Q →* G) (A : Rep.{u, 0, u} ℤ G) :
    uliftIntegralRepresentation (Rep.res f A) ≅
      Rep.res f (uliftIntegralRepresentation A) := by
  apply Rep.mkIso
  exact
    { toLinearEquiv := LinearEquiv.refl (ULift.{u} ℤ) A
      isIntertwining' := fun g ↦ by
        apply LinearMap.ext
        intro x
        rfl }

private noncomputable def ideleFixedIso
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal] :
    (ideleCohomologyRepresentation K L).quotientToInvariants H ≅
      Rep.res (IsGalois.normalAutEquivQuotient H).toMonoidHom
        (ideleCohomologyRepresentation K
          (IntermediateField.fixedField H)) :=
  ((Rep.quotientToInvariantsFunctor (ULift.{u} ℤ) H).mapIso
      (intUIso K L).symm) ≪≫
    uliftInvariantsIso
      (classCokernelRepresentation (K := K) (L := L)) H ≪≫
    uliftIntegralIso (integralFixedIso K L H) ≪≫
    uliftResIso (IsGalois.normalAutEquivQuotient H).toMonoidHom
      (classCokernelRepresentation
        (K := K) (L := IntermediateField.fixedField H)) ≪≫
    ((Rep.resFunctor (IsGalois.normalAutEquivQuotient H).toMonoidHom).mapIso
      (intUIso K (IntermediateField.fixedField H)))

/-- Cohomology of the quotient action on fixed idèle classes is the
cohomology of the idèle-class representation of the fixed field. -/
noncomputable def ideleClassCohomology
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal] (n : ℕ) :
    groupCohomology
        (ideleCohomologyRepresentation K
          (IntermediateField.fixedField H)) n ≃+
      groupCohomology
        ((ideleCohomologyRepresentation K L).quotientToInvariants H) n :=
  (cohomologyMulIso (IsGalois.normalAutEquivQuotient H)
      (ideleCohomologyRepresentation K
        (IntermediateField.fixedField H)) n).toLinearEquiv.toAddEquiv |>.trans
    (((groupCohomology.functor (ULift.{u} ℤ) (Gal(L/K) ⧸ H) n).mapIso
      (ideleFixedIso K L H).symm).toLinearEquiv.toAddEquiv)

private theorem fixed_degree_index
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) :
    Module.finrank K (IntermediateField.fixedField H) = H.index := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H))
  calc
    Module.finrank K (IntermediateField.fixedField H) * Nat.card H =
        Module.finrank K (IntermediateField.fixedField H) *
          Module.finrank (IntermediateField.fixedField H) L := by
      rw [IntermediateField.finrank_fixedField_eq_card]
    _ = Module.finrank K L := Module.finrank_mul_finrank K _ L
    _ = Nat.card Gal(L/K) :=
      (IsGalois.card_aut_eq_finrank (F := K) (E := L)).symm
    _ = Nat.card H * H.index := H.card_mul_index.symm
    _ = H.index * Nat.card H := Nat.mul_comm _ _

private theorem h_1_fixed
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K)) [H.Normal]
    (hzero : IsZero (groupCohomology.H1
      (ideleCohomologyRepresentation K
        (IntermediateField.fixedField H)))) :
    IsZero (groupCohomology.H1
      ((ideleCohomologyRepresentation K L).quotientToInvariants H)) := by
  let e := ideleClassCohomology K L H 1
  letI : Subsingleton (groupCohomology.H1
      (ideleCohomologyRepresentation K
        (IntermediateField.fixedField H))) :=
    ModuleCat.subsingleton_of_isZero hzero
  letI : Subsingleton (groupCohomology.H1
      ((ideleCohomologyRepresentation K L).quotientToInvariants H)) :=
    e.symm.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

private theorem restricted_h_1
    (K L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (H : Subgroup Gal(L/K))
    (hzero : IsZero (groupCohomology.H1
      (ideleCohomologyRepresentation
        (IntermediateField.fixedField H) L))) :
    IsZero (groupCohomology.H1
      (Rep.res H.subtype (ideleCohomologyRepresentation K L))) := by
  let e := restrictedIdeleCohomology K L H 1
  letI : Subsingleton (groupCohomology.H1
      (ideleCohomologyRepresentation
        (IntermediateField.fixedField H) L)) :=
    ModuleCat.subsingleton_of_isZero hzero
  letI : Subsingleton (groupCohomology.H1
      (Rep.res H.subtype (ideleCohomologyRepresentation K L))) :=
    e.symm.injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

set_option maxHeartbeats 1000000 in
-- The final fixed-field comparison packages several dependent representation maps.
set_option maxRecDepth 100000 in
/-- The literal fixed-field idèle-class comparisons required by the
inflation--restriction induction in Lemma VII.5.4. -/
theorem fixedFieldBridge : FixedFieldBridge.{u} := by
  intro K L _ _ _ _ _ _ _ H hnormal
  letI : H.Normal := hnormal
  let E := IntermediateField.fixedField H
  letI : IsGalois E L := inferInstance
  refine ⟨⟨inferInstance, fixed_degree_index K L H, ?_, ?_, ?_, ?_⟩⟩
  · exact h_1_fixed K L H
  · exact restricted_h_1 K L H
  · exact (Nat.card_congr
      (ideleClassCohomology K L H 2).toEquiv).symm
  · exact (Nat.card_congr
      (restrictedIdeleCohomology K L H 2).toEquiv).symm

end

end Submission.CField.CIdeles

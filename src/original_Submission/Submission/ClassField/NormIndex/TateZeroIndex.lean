import Submission.ClassField.NormIndex.InfiniteIdeleCompatibility
import Submission.ClassField.NormIndex.IndexComparison
import Submission.ClassField.Shifting.ExceptionalTateTransport

/-!
# Tate degree zero and the idèle norm index

This file carries out the exact comparison used in Corollary VII.4.4.  It
first transports universe-polymorphic Tate degree zero across an isomorphism
of representations, then identifies the additive representation model with
multiplicative invariants modulo the action norm.  Norm compatibility for the
canonical idèle-extension map turns that quotient into
`C_K / Nm(C_L)`, and the third-isomorphism comparison identifies its
cardinality with the literal index
`[I_K : Kˣ · Nm(I_L)]`.

The only remaining arithmetic input is exactly Lemma VII.4.1: bijectivity of
the canonical map from `C_K` to the fixed idèle classes.  No finiteness or
numerical inequality is included in that input.
-/

namespace Submission.CField.NIndex

open CategoryTheory Rep Representation
open Submission.CField.ICohomo
open Submission.CField.LBrauer
open Submission.CField.Ideles

noncomputable section

universe u v

variable {k : Type v} {G : Type u} [CommRing k] [Group G] [Fintype G]

private noncomputable def pCoinvariantsLinear
    {A B : Rep k G} (e : A ≅ B) :
    A.ρ.Coinvariants ≃ₗ[k] B.ρ.Coinvariants :=
  ((Rep.coinvariantsFunctor k G).mapIso e).toLinearEquiv

private noncomputable def pInvariantsLinear
    {A B : Rep k G} (e : A ≅ B) :
    A.ρ.invariants ≃ₗ[k] B.ρ.invariants :=
  ((Rep.invariantsFunctor k G).mapIso e).toLinearEquiv

private theorem p_coinvariants_linear
    {A B : Rep k G} (e : A ≅ B) (x : A.ρ.Coinvariants) :
    normCoinvariantsInvariants B
        (pCoinvariantsLinear e x) =
      pInvariantsLinear e
        (normCoinvariantsInvariants A x) := by
  induction x using Coinvariants.induction_on with
  | _ y =>
      apply Subtype.ext
      change B.ρ.norm (e.hom y) = e.hom (A.ρ.norm y)
      exact congrArg (fun q : A ⟶ B => q.hom y) (Rep.norm_comm e.hom)

private theorem p_norm_range
    {A B : Rep k G} (e : A ≅ B) :
    (LinearMap.range (normCoinvariantsInvariants A)).map
        (pInvariantsLinear e).toLinearMap =
      LinearMap.range (normCoinvariantsInvariants B) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨pCoinvariantsLinear e z,
      p_coinvariants_linear e z⟩
  · rintro ⟨z, rfl⟩
    refine ⟨(pInvariantsLinear e).symm
      (normCoinvariantsInvariants B z), ?_, ?_⟩
    · refine ⟨(pCoinvariantsLinear e).symm z, ?_⟩
      apply (pInvariantsLinear e).injective
      rw [← p_coinvariants_linear]
      simp
    · simp

noncomputable def tateEquivIso
    {A B : Rep k G} (e : A ≅ B) :
    tateZero A ≃ₗ[k] tateZero B :=
  Submodule.Quotient.equiv
    (LinearMap.range (normCoinvariantsInvariants A))
    (LinearMap.range (normCoinvariantsInvariants B))
    (pInvariantsLinear e) (p_norm_range e)

/-- Additive form of Tate-zero transport.  Stating this separately erases
the choice between the canonical quotient `ℤ`-module structure and the
generic one induced by its additive group. -/
noncomputable def zeroAddIso
    {A B : Rep k G} (e : A ≅ B) :
    tateZero A ≃+ tateZero B := by
  let eLin := tateEquivIso e
  exact
    { toFun := eLin
      invFun := eLin.symm
      left_inv := eLin.left_inv
      right_inv := eLin.right_inv
      map_add' := eLin.map_add }

variable (G M : Type u) [Group G] [Fintype G]
  [CommGroup M] [MulDistribMulAction G M]

private def pRepInvariant
    (x : (Rep.ofMulDistribMulAction G M).ρ.invariants) :
    FMAct.invariants G M :=
  ⟨x.1.toMul, fun g => congrArg Additive.toMul (x.2 g)⟩

private def pRepQuotient :
    (Rep.ofMulDistribMulAction G M).ρ.invariants →+
      Additive (FMAct.invariantsModNorm G M) where
  toFun x := Additive.ofMul
    (QuotientGroup.mk' (FMAct.norm G M).range
      (pRepInvariant G M x))
  map_zero' := by
    apply Additive.toMul.injective
    apply (QuotientGroup.eq_one_iff _).2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp [pRepInvariant, FMAct.norm]
    rfl
  map_add' x y := by
    apply Additive.toMul.injective
    rfl

private theorem p_rep_surjective :
    Function.Surjective (pRepQuotient G M) := by
  intro q
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (FMAct.norm G M).range q.toMul
  let x : (Rep.ofMulDistribMulAction G M).ρ.invariants :=
    ⟨Additive.ofMul y.1, fun g => congrArg Additive.ofMul (y.2 g)⟩
  refine ⟨x, ?_⟩
  apply Additive.toMul.injective
  exact hy

private theorem p_rep_norm (x : M) :
    pRepInvariant G M
        (normCoinvariantsInvariants
          (Rep.ofMulDistribMulAction G M)
          (Coinvariants.mk (Rep.ofMulDistribMulAction G M).ρ
            (Additive.ofMul x))) =
      FMAct.norm G M x := by
  apply Subtype.ext
  change Additive.toMul
      ((Rep.ofMulDistribMulAction G M).ρ.norm (Additive.ofMul x)) =
    ∏ g : G, g • x
  simp only [Representation.norm]
  rw [LinearMap.sum_apply]
  change Additive.toMul
      (∑ g ∈ (Finset.univ : Finset G),
        (Additive.ofMul (g • x) : Additive M)) =
    ∏ g ∈ (Finset.univ : Finset G), g • x
  rw [toMul_sum]
  rfl

private theorem p_rep_invariant :
    (LinearMap.range
        (normCoinvariantsInvariants
          (Rep.ofMulDistribMulAction G M))).toAddSubgroup =
      (pRepQuotient G M).ker := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Coinvariants.induction_on with
    | _ y =>
        apply AddMonoidHom.mem_ker.mpr
        apply Additive.toMul.injective
        change QuotientGroup.mk' (FMAct.norm G M).range
            (pRepInvariant G M
              (normCoinvariantsInvariants
                (Rep.ofMulDistribMulAction G M)
                (Coinvariants.mk (Rep.ofMulDistribMulAction G M).ρ y))) = 1
        have hnorm := p_rep_norm G M y.toMul
        calc
          QuotientGroup.mk' (FMAct.norm G M).range
              (pRepInvariant G M
                (normCoinvariantsInvariants
                  (Rep.ofMulDistribMulAction G M)
                  (Coinvariants.mk (Rep.ofMulDistribMulAction G M).ρ y))) =
              QuotientGroup.mk' (FMAct.norm G M).range
                (FMAct.norm G M y.toMul) := by
                  simpa using congrArg
                    (QuotientGroup.mk' (FMAct.norm G M).range) hnorm
          _ = 1 := (QuotientGroup.eq_one_iff _).2 ⟨y.toMul, rfl⟩
  · intro hx
    have hxq : QuotientGroup.mk' (FMAct.norm G M).range
        (pRepInvariant G M x) = 1 := by
      exact congrArg Additive.toMul (AddMonoidHom.mem_ker.mp hx)
    obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).1 hxq
    refine ⟨Coinvariants.mk (Rep.ofMulDistribMulAction G M).ρ
      (Additive.ofMul y), ?_⟩
    apply Subtype.ext
    have hnorm := p_rep_norm G M y
    exact congrArg Additive.ofMul
      ((congrArg Subtype.val hnorm).trans (congrArg Subtype.val hy))

noncomputable def tateInvariantsMod :
    tateZero (Rep.ofMulDistribMulAction G M) ≃+
      Additive (FMAct.invariantsModNorm G M) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (p_rep_invariant G M)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (pRepQuotient G M)
      (p_rep_surjective G M))

variable {K L : Type u} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

local instance tateZeroGaloisFintype :
    Fintype Gal(L/K) := Fintype.ofFinite Gal(L/K)

private abbrev CK :=
  IdeleClassGroup (NumberField.RingOfIntegers K) K

private abbrev CL :=
  IdeleClassGroup (NumberField.RingOfIntegers L) L

/-- The two concrete descriptions of Galois-fixed idèle classes agree. -/
noncomputable def fixedClassesInvariants :
    letI := ideleDistribAction (K := K) (L := L)
    fixedIdeleClasses (K := K) (L := L) ≃*
      FMAct.invariants Gal(L/K) (CL (L := L)) := by
  letI := ideleDistribAction (K := K) (L := L)
  exact
    { toFun := fun c => ⟨c.1, c.2⟩
      invFun := fun c => ⟨c.1, c.2⟩
      left_inv := fun c => by apply Subtype.ext; rfl
      right_inv := fun c => by apply Subtype.ext; rfl
      map_mul' := fun _ _ => by apply Subtype.ext; rfl }

/-- A bijective canonical class map identifies base idèle classes with the
invariants in the representation-theoretic model. -/
noncomputable def ideleClassFixed
    (E : IEData (K := K) (L := L))
    (hbij : Function.Bijective E.class_map_fixed) :
    letI := ideleDistribAction (K := K) (L := L)
    CK (K := K) ≃*
      FMAct.invariants Gal(L/K) (CL (L := L)) := by
  letI := ideleDistribAction (K := K) (L := L)
  exact (MulEquiv.ofBijective E.class_map_fixed hbij).trans
    (fixedClassesInvariants (K := K) (L := L))

theorem idele_fixed_norm
    (E : IEData (K := K) (L := L))
    (hbij : Function.Bijective E.class_map_fixed)
    (hnorm : E.NormCompatible) (c : CL (L := L)) :
    letI := ideleDistribAction (K := K) (L := L)
    ideleClassFixed E hbij
        (canonicalIdeleNorm (K := K) (L := L) c) =
      FMAct.norm Gal(L/K) (CL (L := L)) c := by
  letI := ideleDistribAction (K := K) (L := L)
  apply Subtype.ext
  exact E.classm_idele_eqact hnorm c

private theorem action_comap_canonical
    (E : IEData (K := K) (L := L))
    (hbij : Function.Bijective E.class_map_fixed)
    (hnorm : E.NormCompatible) :
    letI := ideleDistribAction (K := K) (L := L)
    (FMAct.norm Gal(L/K) (CL (L := L))).range ≤
      (canonicalIdeleNorm (K := K) (L := L)).range.comap
        (ideleClassFixed E hbij).symm.toMonoidHom := by
  letI := ideleDistribAction (K := K) (L := L)
  rintro _ ⟨c, rfl⟩
  refine ⟨c, ?_⟩
  exact (ideleClassFixed E hbij).eq_symm_apply.mpr
    (idele_fixed_norm E hbij hnorm c)

private theorem canonical_comap_action
    (E : IEData (K := K) (L := L))
    (hbij : Function.Bijective E.class_map_fixed)
    (hnorm : E.NormCompatible) :
    letI := ideleDistribAction (K := K) (L := L)
    (canonicalIdeleNorm (K := K) (L := L)).range ≤
      (FMAct.norm Gal(L/K) (CL (L := L))).range.comap
        (ideleClassFixed E hbij).toMonoidHom := by
  letI := ideleDistribAction (K := K) (L := L)
  rintro _ ⟨c, rfl⟩
  exact ⟨c, (idele_fixed_norm E hbij hnorm c).symm⟩

/-- Under the fixed-class isomorphism, quotienting by the action norm is
the same as quotienting base idèle classes by the canonical norm. -/
noncomputable def ideleInvariantsMod
    (E : IEData (K := K) (L := L))
    (hbij : Function.Bijective E.class_map_fixed)
    (hnorm : E.NormCompatible) :
    letI := ideleDistribAction (K := K) (L := L)
    FMAct.invariantsModNorm Gal(L/K) (CL (L := L)) ≃*
      CK (K := K) ⧸
        (canonicalIdeleNorm (K := K) (L := L)).range := by
  letI := ideleDistribAction (K := K) (L := L)
  exact
    { toFun := QuotientGroup.map
        (FMAct.norm Gal(L/K) (CL (L := L))).range
        (canonicalIdeleNorm (K := K) (L := L)).range
        (ideleClassFixed E hbij).symm.toMonoidHom
        (action_comap_canonical E hbij hnorm)
      invFun := QuotientGroup.map
        (canonicalIdeleNorm (K := K) (L := L)).range
        (FMAct.norm Gal(L/K) (CL (L := L))).range
        (ideleClassFixed E hbij).toMonoidHom
        (canonical_comap_action E hbij hnorm)
      left_inv := fun q => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
          (FMAct.norm Gal(L/K) (CL (L := L))).range q
        apply congrArg (QuotientGroup.mk'
          (FMAct.norm Gal(L/K) (CL (L := L))).range)
        exact (ideleClassFixed E hbij).apply_symm_apply x
      right_inv := fun q => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
          (canonicalIdeleNorm (K := K) (L := L)).range q
        apply congrArg (QuotientGroup.mk'
          (canonicalIdeleNorm (K := K) (L := L)).range)
        exact (ideleClassFixed E hbij).symm_apply_apply x
      map_mul' := fun x y => map_mul _ x y }

set_option maxHeartbeats 3000000 in
-- Keeping the three cardinal transports separate avoids asking the
-- elaborator to normalize one large composite dependent equivalence.
set_option maxRecDepth 100000 in
theorem nat_card_tate
    (E : IEData (K := K) (L := L))
    (hbij : Function.Bijective E.class_map_fixed)
    (hnorm : E.NormCompatible) :
    Nat.card
        (tateZero
          (classCokernelRepresentation (K := K) (L := L))) =
      Nat.card
        (CK (K := K) ⧸
          (canonicalIdeleNorm (K := K) (L := L)).range) := by
  letI := ideleDistribAction (K := K) (L := L)
  calc
    Nat.card
        (tateZero
          (classCokernelRepresentation (K := K) (L := L))) =
        Nat.card
          (tateZero
            (explicitIdeleRepresentation (K := K) (L := L))) :=
      Nat.card_congr (zeroAddIso
        (cokernelIsoExplicit (K := K) (L := L))).toEquiv
    _ = Nat.card
        (Additive
          (FMAct.invariantsModNorm Gal(L/K) (CL (L := L)))) :=
      Nat.card_congr
        (tateInvariantsMod
          Gal(L/K) (CL (L := L))).toEquiv
    _ = Nat.card
        (Additive
          (CK (K := K) ⧸
            (canonicalIdeleNorm (K := K) (L := L)).range)) :=
      Nat.card_congr
        (ideleInvariantsMod
          E hbij hnorm).toAdditive.toEquiv
    _ = Nat.card
        (CK (K := K) ⧸
          (canonicalIdeleNorm (K := K) (L := L)).range) := rfl

theorem tate_principal_index
    (E : IEData (K := K) (L := L))
    (hbij : Function.Bijective E.class_map_fixed)
    (hnorm : E.NormCompatible) :
    Nat.card
        (tateZero
          (classCokernelRepresentation (K := K) (L := L))) =
      (principalIdeles (NumberField.RingOfIntegers K) K ⊔
        ideleNormSubgroup (K := K) (L := L)).index := by
  rw [nat_card_tate E hbij hnorm]
  exact nat_principal_index K L

/-- The canonical, rather than merely existential, form of Lemma VII.4.1. -/
def TateIndexFormula : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L],
    Function.Bijective
      (canonicalExtensionData (K := K) (L := L)).class_map_fixed

/-- The remaining two arithmetic bridges from Lemma VII.4.1 imply its
canonical fixed-class formulation. -/
theorem tate_formula_bridges
    (hprincipal : PrincipalDescentBridge.{u})
    (hlift : FixedLiftingBridge.{u}) :
    TateIndexFormula.{u} := by
  intro K L _ _ _ _ _ _ _
  let E := canonicalExtensionData (K := K) (L := L)
  constructor
  · apply (MonoidHom.ker_eq_bot_iff E.class_map_fixed).mp
    ext c
    constructor
    · intro hc
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
        (principalIdeles (NumberField.RingOfIntegers K) K) c
      have hc' := congrArg Subtype.val hc
      change E.classMap
          (QuotientGroup.mk'
            (principalIdeles (NumberField.RingOfIntegers K) K) x) = 1 at hc'
      rw [E.classMap_mk] at hc'
      apply Subgroup.mem_bot.mpr
      apply (QuotientGroup.eq_one_iff x).mpr
      rw [← hprincipal K L E]
      exact (QuotientGroup.eq_one_iff (E.toMonoidHom x)).mp hc'
    · intro hc
      have hc' : c = 1 := Subgroup.mem_bot.mp hc
      subst c
      exact E.class_map_fixed.ker.one_mem
  · intro c
    obtain ⟨x, hx⟩ := hlift K L E c
    exact ⟨QuotientGroup.mk'
      (principalIdeles (NumberField.RingOfIntegers K) K) x, hx⟩

set_option maxHeartbeats 1000000 in
-- The index comparison unfolds nested quotient and norm-principal-idèle maps.
set_option maxRecDepth 100000 in
private theorem canonical_principal_index
    (hbij : Function.Bijective
      (canonicalExtensionData (K := K) (L := L)).class_map_fixed) :
    Nat.card
        (tateZero
          (classCokernelRepresentation (K := K) (L := L))) =
      (principalIdeles (NumberField.RingOfIntegers K) K ⊔
        ideleNormSubgroup (K := K) (L := L)).index := by
  exact tate_principal_index
    (canonicalExtensionData (K := K) (L := L)) hbij
    (canonical_idele_compatible (K := K) (L := L))

set_option maxHeartbeats 3000000 in
-- Reducing the nested quotient equivalences and the cyclic-group instances
-- requires a larger elaboration budget.
set_option maxRecDepth 100000 in
/-- Norm compatibility and the canonical fixed-class theorem discharge the
cardinality bridge in Corollary VII.4.4. -/
theorem tate_bridge_fixed
    (h41 : TateIndexFormula.{u}) :
    TateIndexBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _
  exact canonical_principal_index
    (K := K) (L := L) (h41 K L)

theorem tate_bridge_bridges
    (hprincipal : PrincipalDescentBridge.{u})
    (hlift : FixedLiftingBridge.{u}) :
    TateIndexBridge.{u} :=
  tate_bridge_fixed
    (tate_formula_bridges hprincipal hlift)

end

end Submission.CField.NIndex

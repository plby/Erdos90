import Mathlib.Algebra.Module.ULift
import Submission.ClassField.LocalFields.NormSubgroups
import Submission.ClassField.Shifting.GroupPeriodicityOdd
import Submission.ClassField.LocalBrauer.CohomologyTransport

/-!
# The global norm quotient as cyclic degree-two cohomology

This file supplies the universe-resized global comparison used in the
cohomological proof of the Hasse norm theorem.  The coefficient ring is
`ULift ℤ`, so it lives in the same universe as the Galois group, while the
underlying additive group and Galois action remain unchanged.
-/

namespace Submission.CField.HNorm

open Representation
open Submission.CField.LFTheory
open Submission.CField.Shifting
open Submission.CField.LBrauer
open groupCohomology

noncomputable section

universe u

/-- A multiplicative action, written additively and linearly over the
universe lift of `ℤ`. -/
def uliftMulRepresentation
    {G M : Type u} [Group G] [CommGroup M] [MulDistribMulAction G M] :
    Rep (ULift.{u} ℤ) G :=
  Rep.of
    { toFun := fun g =>
        { toFun := fun x : Additive M => Additive.ofMul (g • x.toMul)
          map_add' := fun x y =>
            congrArg Additive.ofMul (smul_mul' g x.toMul y.toMul)
          map_smul' := fun r x =>
            (Representation.ofMulDistribMulAction G M g).map_smul r.down x }
      map_one' := by
        ext x
        simp
      map_mul' := by
        intro g h
        ext x
        simp [mul_smul] }

section MultiplicativeAction

variable (G M : Type u) [Group G] [Fintype G]
  [CommGroup M] [MulDistribMulAction G M]

/-- Convert an invariant of the resized additive representation back to a
multiplicative invariant. -/
private def uliftRepInvariant
    (x : (uliftMulRepresentation (G := G) (M := M)).ρ.invariants) :
    FMAct.invariants G M :=
  ⟨x.1.toMul, fun g => congrArg Additive.toMul (x.2 g)⟩

/-- The quotient map from resized representation invariants to
multiplicative invariants modulo norms, written additively. -/
private def uliftRepQuotient :
    (uliftMulRepresentation (G := G) (M := M)).ρ.invariants →+
      Additive (FMAct.invariantsModNorm G M) where
  toFun x := Additive.ofMul
    (QuotientGroup.mk' (FMAct.norm G M).range
      (uliftRepInvariant G M x))
  map_zero' := by
    apply Additive.toMul.injective
    apply (QuotientGroup.eq_one_iff _).2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp [uliftRepInvariant, FMAct.norm]
    rfl
  map_add' x y := by
    apply Additive.toMul.injective
    rfl

private theorem ulift_rep_surjective :
    Function.Surjective (uliftRepQuotient G M) := by
  intro q
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (FMAct.norm G M).range q.toMul
  let x : (uliftMulRepresentation (G := G) (M := M)).ρ.invariants :=
    ⟨Additive.ofMul y.1, fun g => congrArg Additive.ofMul (y.2 g)⟩
  refine ⟨x, ?_⟩
  apply Additive.toMul.injective
  exact hy

private theorem ulift_rep_invariant (x : M) :
    uliftRepInvariant G M
        (normCoinvariantsInvariants
          (uliftMulRepresentation (G := G) (M := M))
          (Coinvariants.mk (uliftMulRepresentation (G := G) (M := M)).ρ
            (Additive.ofMul x))) =
      FMAct.norm G M x := by
  apply Subtype.ext
  change Additive.toMul
      ((uliftMulRepresentation (G := G) (M := M)).ρ.norm
        (Additive.ofMul x)) = ∏ g : G, g • x
  simp only [Representation.norm]
  rw [LinearMap.sum_apply]
  change Additive.toMul
      (∑ g ∈ (Finset.univ : Finset G),
        (Additive.ofMul (g • x) : Additive M)) =
    ∏ g ∈ (Finset.univ : Finset G), g • x
  rw [toMul_sum]
  rfl

private theorem ulift_range_invariant :
    (LinearMap.range
        (normCoinvariantsInvariants
          (uliftMulRepresentation (G := G) (M := M)))).toAddSubgroup =
      (uliftRepQuotient G M).ker := by
  ext x
  constructor
  · rintro ⟨q, rfl⟩
    induction q using Coinvariants.induction_on with
    | _ y =>
        apply AddMonoidHom.mem_ker.mpr
        apply Additive.toMul.injective
        change QuotientGroup.mk' (FMAct.norm G M).range
            (uliftRepInvariant G M
              (normCoinvariantsInvariants
                (uliftMulRepresentation (G := G) (M := M))
                (Coinvariants.mk
                  (uliftMulRepresentation (G := G) (M := M)).ρ y))) = 1
        have hnorm := ulift_rep_invariant G M y.toMul
        calc
          QuotientGroup.mk' (FMAct.norm G M).range
              (uliftRepInvariant G M
                (normCoinvariantsInvariants
                  (uliftMulRepresentation (G := G) (M := M))
                  (Coinvariants.mk
                    (uliftMulRepresentation (G := G) (M := M)).ρ y))) =
              QuotientGroup.mk' (FMAct.norm G M).range
                (FMAct.norm G M y.toMul) := by
                  simpa using congrArg
                    (QuotientGroup.mk' (FMAct.norm G M).range) hnorm
          _ = 1 := (QuotientGroup.eq_one_iff _).2 ⟨y.toMul, rfl⟩
  · intro hx
    have hxq : QuotientGroup.mk' (FMAct.norm G M).range
        (uliftRepInvariant G M x) = 1 := by
      exact congrArg Additive.toMul (AddMonoidHom.mem_ker.mp hx)
    obtain ⟨y, hy⟩ := (QuotientGroup.eq_one_iff _).1 hxq
    refine ⟨Coinvariants.mk
      (uliftMulRepresentation (G := G) (M := M)).ρ
      (Additive.ofMul y), ?_⟩
    apply Subtype.ext
    have hnorm := ulift_rep_invariant G M y
    exact congrArg Additive.ofMul
      ((congrArg Subtype.val hnorm).trans (congrArg Subtype.val hy))

/-- Tate degree zero of the resized multiplicative representation is the
additive form of multiplicative invariants modulo norms. -/
noncomputable def uliftTateInvariants :
    tateCohomologyZero (uliftMulRepresentation (G := G) (M := M)) ≃+
      Additive (FMAct.invariantsModNorm G M) :=
  (QuotientAddGroup.quotientAddEquivOfEq
      (ulift_range_invariant G M)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (uliftRepQuotient G M)
      (ulift_rep_surjective G M))

end MultiplicativeAction

section Galois

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- The universe-resized representation on the multiplicative group of a
finite Galois extension. -/
noncomputable abbrev hasseGlobalRepresentation :
    Rep (ULift.{u} ℤ) Gal(L/K) :=
  uliftMulRepresentation (G := Gal(L/K)) (M := Lˣ)

private def unitsInvariantsUlift :
    Kˣ →* FMAct.invariants Gal(L/K) Lˣ where
  toFun x := ⟨Units.map (algebraMap K L) x, by
    intro sigma
    apply Units.ext
    simp⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by apply Subtype.ext; simp

private theorem invariants_ulift_bijective :
    Function.Bijective (unitsInvariantsUlift K L) := by
  constructor
  · intro x y hxy
    apply Units.ext
    apply (algebraMap K L).injective
    have h := congrArg
      (fun z : FMAct.invariants Gal(L/K) Lˣ => ((z.1 : Lˣ) : L)) hxy
    simpa [unitsInvariantsUlift] using h
  · intro x
    have hfixed : ∀ sigma : Gal(L/K), sigma (x.1 : L) = (x.1 : L) := by
      intro sigma
      exact congrArg Units.val (x.2 sigma)
    obtain ⟨a, ha⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed
        (F := K) (E := L) (x.1 : L)).2 hfixed
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, map_zero] at ha
      exact x.1.ne_zero ha.symm
    refine ⟨Units.mk0 a ha0, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact ha

private noncomputable def baseInvariantsUlift :
    Kˣ ≃* FMAct.invariants Gal(L/K) Lˣ :=
  MulEquiv.ofBijective (unitsInvariantsUlift K L)
    (invariants_ulift_bijective K L)

private theorem base_invariants_ulift (x : Lˣ) :
    baseInvariantsUlift K L (normOnUnits K L x) =
      FMAct.norm Gal(L/K) Lˣ x := by
  apply Subtype.ext
  apply Units.ext
  simpa [baseInvariantsUlift,
    unitsInvariantsUlift, normOnUnits,
    FMAct.norm] using
      (Algebra.norm_eq_prod_automorphisms K (x : L))

private theorem galois_comap_ulift :
    (FMAct.norm Gal(L/K) Lˣ).range ≤
      (normOnUnits K L).range.comap
        (baseInvariantsUlift K L).symm.toMonoidHom := by
  rintro _ ⟨x, rfl⟩
  refine ⟨x, ?_⟩
  exact (baseInvariantsUlift K L).eq_symm_apply.mpr
    (base_invariants_ulift K L x)

private theorem base_comap_ulift :
    (normOnUnits K L).range ≤
      (FMAct.norm Gal(L/K) Lˣ).range.comap
        (baseInvariantsUlift K L).toMonoidHom := by
  rintro _ ⟨x, rfl⟩
  exact ⟨x,
    (base_invariants_ulift K L x).symm⟩

private noncomputable def galoisInvariantsUlift :
    FMAct.invariantsModNorm Gal(L/K) Lˣ ≃*
      Kˣ ⧸ normSubgroup K L where
  toFun := QuotientGroup.map
    (FMAct.norm Gal(L/K) Lˣ).range
    (normOnUnits K L).range
    (baseInvariantsUlift K L).symm.toMonoidHom
    (galois_comap_ulift K L)
  invFun := QuotientGroup.map
    (normOnUnits K L).range
    (FMAct.norm Gal(L/K) Lˣ).range
    (baseInvariantsUlift K L).toMonoidHom
    (base_comap_ulift K L)
  left_inv q := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (FMAct.norm Gal(L/K) Lˣ).range q
    apply congrArg (QuotientGroup.mk'
      (FMAct.norm Gal(L/K) Lˣ).range)
    exact (baseInvariantsUlift K L).apply_symm_apply x
  right_inv q := by
    obtain ⟨x, rfl⟩ :=
      QuotientGroup.mk'_surjective (normOnUnits K L).range q
    apply congrArg (QuotientGroup.mk' (normOnUnits K L).range)
    exact (baseInvariantsUlift K L).symm_apply_apply x
  map_mul' x y := map_mul _ x y

/-- For a finite Galois extension in `Type u`, Tate degree zero of the
resized units representation is the literal field-unit norm quotient. -/
noncomputable def uliftGaloisTate
    : tateCohomologyZero (hasseGlobalRepresentation K L) ≃+
      Additive (Kˣ ⧸ normSubgroup K L) :=
  (uliftTateInvariants Gal(L/K) Lˣ).trans
    (galoisInvariantsUlift K L).toAdditive

set_option synthInstance.maxHeartbeats 200000 in
-- The quotient and cohomology structures make additive instance synthesis deep.
/-- For a cyclic finite Galois extension, the literal global norm quotient
is additively equivalent to degree-two cohomology of the resized global
units representation. -/
noncomputable def hasseGlobal2
    (hcyclic : IsCyclic Gal(L/K)) :
    Additive (Kˣ ⧸ normSubgroup K L) ≃+
      H2 (hasseGlobalRepresentation K L) := by
  letI : IsCyclic Gal(L/K) := hcyclic
  letI : CommGroup Gal(L/K) := IsCyclic.commGroup
  let g : Gal(L/K) :=
    Classical.choose (IsCyclic.exists_generator (α := Gal(L/K)))
  have hg : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers g :=
    Classical.choose_spec (IsCyclic.exists_generator (α := Gal(L/K)))
  exact (uliftGaloisTate K L).symm.trans
    (tateCohomologyTwo
      (hasseGlobalRepresentation K L) g hg).toAddEquiv

end Galois

end

end Submission.CField.HNorm

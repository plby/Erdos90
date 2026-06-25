import Submission.ClassField.BrauerLocalization.FiniteZeroDirect
import Submission.ClassField.BrauerLocalization.Relative2Comparison
import Submission.ClassField.LocalBrauer.FiniteRelativeCardinality

/-!
# Finite local relative Brauer cardinality without invariant base change

The direct local Herbrand calculation identifies Tate degree zero of the
completed unit group with a group of order the local extension degree.
Transport through cyclic periodicity, Shapiro, and crossed products therefore
gives the same cardinality for the relative Brauer group.  Together with the
canonical local invariant, this is enough to recognize every degree-torsion
class as relative, and hence to obtain the local vanishing used in VIII.4.2
without the full local-invariant base-change formula.
-/

namespace Submission.CField.BLoc

open CategoryTheory Representation
open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Shifting
open Submission.CField.BGroups
open Submission.CField.CProduca
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.HNorm
open groupCohomology

noncomputable section

universe u

set_option synthInstance.maxHeartbeats 500000 in
-- Cyclic periodicity and the two completion-group presentations elaborate together.
set_option maxHeartbeats 5000000 in
/-- For a finite completion of a cyclic number-field extension, the local
relative Brauer group has cardinality equal to the completion degree. -/
theorem relative_brauer_direct
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    let v := (FinitePlace.mk P).val
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    Nat.card (relativeBrauerGroup v.Completion w.1.Completion) =
      Module.finrank v.Completion w.1.Completion := by
  let v := (FinitePlace.mk P).val
  let W := CompletionPlacesAbove (L := L) v
  let H := CompletionPlaceStabilizer v w
  letI : Fintype H := Fintype.ofFinite H
  letI : IsCyclic H := Subgroup.isCyclic H
  letI : CommGroup H := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : Valuation.Compatible
      (NormedField.valuation (K := v.Completion)) :=
    Valuation.Compatible.ofValuation
      (NormedField.valuation (K := v.Completion))
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Finite W := absolute_extensions_separable v
  letI : Nonempty W := absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K) W :=
    completion_above_pretransitive P
  letI : Fact (AbsoluteValue.LiesOver w.1 v) := ⟨w.2⟩
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Submission.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  let A := placeUnitsRepresentation v w
  let eTate : tateZero A ≃+
      H2 (uliftIntegralRepresentation A) :=
    (tateIntLift A).trans
      (tateCohomologyTwo
        (uliftIntegralRepresentation A) g hg).toAddEquiv
  let ePresentation : H2 (uliftIntegralRepresentation A) ≃+
      H2 (hasseUnitsRepresentation v w) :=
    ((groupCohomology.functor (ULift.{u} ℤ) H 2).mapIso
      (uliftIsoHasse
        (K := K) (L := L) v w)).toLinearEquiv.toAddEquiv
  let eLocal := h2Stabilizer
    (K := K) (L := L) v w (fun x y ↦ (FinitePlace.mk P).add_le x y)
  let eBrauer := relativeBrauer2
    v.Completion w.1.Completion
  let e : tateZero A ≃+
      Additive (relativeBrauerGroup v.Completion w.1.Completion) :=
    eTate.trans (ePresentation.trans (eLocal.symm.trans eBrauer.symm))
  have hTate :=
    tate_cardinality_direct
      (K := K) (L := L) P w
  calc
    Nat.card (relativeBrauerGroup v.Completion w.1.Completion) =
        Nat.card (tateZero A) :=
      Nat.card_congr e.symm.toEquiv
    _ = Nat.card H := hTate.2
    _ = Nat.card (absoluteValueDecomposition v w.1) := by
      change Nat.card (CompletionPlaceStabilizer v w) =
        Nat.card (absoluteValueDecomposition v w.1)
      rw [hasse_stabilizer_decomposition]
    _ = Module.finrank v.Completion w.1.Completion :=
      (finrank_decomposition_card P w).symm

/-- Universe-polymorphic cardinality-to-invariant equivalence for a finite
Galois extension of a nonarchimedean local field. -/
noncomputable def torsionCardinalityDirect
    (k E : Type u)
    [NontriviallyNormedField k] [IsUltrametricDist k] [ValuativeRel k]
    [IsNonarchimedeanLocalField k]
    [Valuation.Compatible (NormedField.valuation (K := k))]
    [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E]
    (hcard : Nat.card (relativeBrauerGroup k E) = Module.finrank k E) :
    relativeBrauerGroup k E ≃*
      Multiplicative (localInvariantTorsion (Module.finrank k E)) := by
  let n := Module.finrank k E
  letI : NeZero n :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := k) (M := E))⟩
  let f : relativeBrauerGroup k E →*
      Multiplicative (localInvariantTorsion n) :=
    { toFun := fun x ↦ ⟨carryBrauerInvariant k x.1, by
          change n • (carryBrauerInvariant k x.1).toAdd = 0
          have hx : (carryBrauerInvariant k x.1) ^ n = 1 := by
            rw [← map_pow]
            have hxrel : x ^ n = 1 :=
              relative_brauer_one k E x
            have hxval : x.1 ^ n = 1 := by
              simpa using congrArg Subtype.val hxrel
            rw [hxval, map_one]
          exact congrArg Multiplicative.toAdd hx
          ⟩
      map_one' := by
        apply Subtype.ext
        exact map_one (carryBrauerInvariant k)
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact map_mul (carryBrauerInvariant k) x.1 y.1 }
  letI : Finite (relativeBrauerGroup k E) :=
    Nat.finite_of_card_ne_zero <| by
      rw [hcard]
      exact NeZero.ne n
  letI : Finite (localInvariantTorsion n) :=
    Finite.of_equiv (ZMod n) (torsionZMod n)
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply (carryBrauerInvariant k).injective
    exact congrArg (fun z : Multiplicative (localInvariantTorsion n) ↦
      ((z.toAdd : localInvariantTorsion n) : LocalInvariant)) hxy
  have hcards : Nat.card (relativeBrauerGroup k E) =
      Nat.card (Multiplicative (localInvariantTorsion n)) := by
    change Nat.card (relativeBrauerGroup k E) =
      Nat.card (localInvariantTorsion n)
    calc
      Nat.card (relativeBrauerGroup k E) = n := hcard
      _ = Nat.card (ZMod n) := (Nat.card_zmod n).symm
      _ = Nat.card (localInvariantTorsion n) :=
        Nat.card_congr (torsionZMod n).toEquiv
  exact MulEquiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).2 ⟨hf, hcards⟩)

/-- If the relative Brauer group has the expected cardinality, degree-torsion
of the canonical invariant is exactly the kernel of scalar extension. -/
theorem brauer_nsmul_cardinality
    (k E : Type u)
    [NontriviallyNormedField k] [IsUltrametricDist k] [ValuativeRel k]
    [IsNonarchimedeanLocalField k]
    [Valuation.Compatible (NormedField.valuation (K := k))]
    [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E]
    (hcard : Nat.card (relativeBrauerGroup k E) = Module.finrank k E)
    (x : Additive (BrauerGroup k)) (m : ℕ)
    (hx : m • (carryBrauerInvariant k x.toMul).toAdd = 0)
    (hdegree : m ∣ Module.finrank k E) :
    brauerBaseChange k E x.toMul = 1 := by
  let n := Module.finrank k E
  letI : NeZero n :=
    ⟨Nat.ne_of_gt (Module.finrank_pos (R := k) (M := E))⟩
  have hn : n •
      (carryBrauerInvariant k x.toMul).toAdd = 0 := by
    obtain ⟨d, hd⟩ := hdegree
    change Module.finrank k E •
      (carryBrauerInvariant k x.toMul).toAdd = 0
    rw [hd, mul_nsmul, hx, nsmul_zero]
  let t : Multiplicative (localInvariantTorsion n) :=
    Multiplicative.ofAdd
      ⟨(carryBrauerInvariant k x.toMul).toAdd, hn⟩
  let e := torsionCardinalityDirect
    k E hcard
  let y : relativeBrauerGroup k E := e.symm t
  have hey : e y = t := e.apply_symm_apply t
  have hinv : carryBrauerInvariant k y.1 =
      carryBrauerInvariant k x.toMul := by
    exact congrArg (fun z : Multiplicative (localInvariantTorsion n) ↦
      Multiplicative.ofAdd
        ((z.toAdd : localInvariantTorsion n) : LocalInvariant)) hey
  have hy : y.1 = x.toMul :=
    (carryBrauerInvariant k).injective hinv
  rw [← relative_brauer_group]
  rw [← hy]
  exact y.property

end

end Submission.CField.BLoc

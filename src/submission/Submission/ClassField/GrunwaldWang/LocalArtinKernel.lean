import Submission.ClassField.Reciprocity.ArtinMapStatements
import Submission.NumberTheory.Galois.PlaceCompletionDegree
import Submission.ClassField.IdeleCohomology.CompletionProductAction

/-!
# Theorem VIII.2.3: finite local Artin kernels

This file extracts from the finite-place local Artin predicate the norm
kernel in the absolute-value completion model.  The remaining comparison for
Theorem VIII.2.3 is between this completion model and the prime-adic model
used by `finiteCompletionNorm`.
-/

namespace Submission.CField.GWang

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.Ideles
open Submission.CField.Recip

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

set_option synthInstance.maxHeartbeats 300000 in
-- The nested local subextension and completion equivalences make instance
-- synthesis substantially more expensive than the default budget.
set_option maxHeartbeats 2000000 in
/-- A finite local Artin map has, after transporting the base completion to
the prime-adic completion, the norm subgroup of the absolute-value
completion appearing in its local reciprocity datum as its kernel. -/
theorem artin_ker_abstract
    (L : FASubext K) [NumberField L.1]
    (P : HeightOneSpectrum (RingOfIntegers K))
    (Q : UpperPrimeFactors (K := K) (L := L.1) P)
    (f : (P.adicCompletion K)ˣ →* Gal(L.1/K))
    (hf : LayerLocalArtin L P Q f) :
    ∃ (w : AbsoluteValue L.1 ℝ)
      (hwv : AbsoluteValue.LiesOver w (FinitePlace.mk P).val),
      w.IsEquiv
          (FinitePlace.mk (upperPrime (K := K) (L := L.1) P Q)).val ∧
      letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
        ⟨absolute_value_nontrivial P⟩
      letI : Algebra (FinitePlace.mk P).val.Completion w.Completion :=
        (completionLies (FinitePlace.mk P).val w hwv).toAlgebra
      ∃ hfinite : Module.Finite
          (FinitePlace.mk P).val.Completion w.Completion,
        letI : Module.Finite
            (FinitePlace.mk P).val.Completion w.Completion := hfinite
        f.ker =
          (normSubgroup (FinitePlace.mk P).val.Completion w.Completion).comap
            (Units.map
              (placeCompletionAdic P).symm.toRingHom) := by
  rcases hf with ⟨w, hwv, hwq, e, hformula, _hnormalized⟩
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial := ⟨absolute_value_nontrivial P⟩
  letI : NontriviallyNormedField v.Completion :=
    placeNontriviallyNormed P
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : ValuativeRel v.Completion :=
    placeValuativeRel P
  letI : IsNonarchimedeanLocalField v.Completion :=
    placeNonarchimedeanField P
  letI : Fact (AbsoluteValue.LiesOver w v) := ⟨hwv⟩
  letI : Algebra v.Completion w.Completion :=
    (completionLies v w hwv).toAlgebra
  let wAbove : Submission.CField.ICohomo.CompletionPlacesAbove
      (L := L.1) v := ⟨w, hwv⟩
  letI : FiniteDimensional v.Completion w.Completion :=
    placeCompletionDimensional v wAbove
  let hfinite : Module.Finite v.Completion w.Completion := inferInstance
  refine ⟨w, hwv, hwq, hfinite, ?_⟩
  letI : Module.Finite v.Completion w.Completion := hfinite
  ext x
  simp only [MonoidHom.mem_ker, Subgroup.mem_comap]
  rw [hformula x]
  let F : Gal(w.Completion/v.Completion) → Gal(L.1/K) := fun sigma =>
    ((decompositionCompletionExtension v w).symm
      sigma : Gal(L.1/K))
  have hF_inj : Function.Injective F := by
    intro a b hab
    have hab' :
        (decompositionCompletionExtension v w).symm
            a =
          (decompositionCompletionExtension v w).symm
            b :=
      Subtype.ext hab
    exact (decompositionCompletionExtension v w).symm.injective
      hab'
  have hF_one : F 1 = 1 := by
    dsimp only [F]
    rw [map_one (decompositionCompletionExtension v w).symm]
    rfl
  rw [← hF_one]
  let y : v.Completionˣ := Units.map
    (placeCompletionAdic P).symm.toRingHom x
  change F (e (QuotientGroup.mk'
      (normSubgroup v.Completion w.Completion) y)) = F 1 ↔ _
  rw [hF_inj.eq_iff]
  rw [← map_one e, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff y

end

end Submission.CField.GWang

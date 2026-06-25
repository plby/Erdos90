import Submission.ClassField.Shifting.SolvableGroup
import Submission.ClassField.NormIndex.IdeleTowerTransitivity
import Submission.ClassField.NormIndex.CyclicSubextensionData

/-!
# The cyclic subextension used in Lemma VII.4.5

A nontrivial finite solvable Galois extension has a proper normal subgroup
with cyclic quotient.  Its fixed field is therefore a nontrivial cyclic
Galois extension of the base field.
-/

namespace Submission.CField.NIndex

open Submission.CField.Shifting
open Submission.CField.ICohomo
open Submission.CField.Ideles

noncomputable section

universe u

private abbrev IK (K : Type u) [Field K] [NumberField K] :=
  IdeleGroup (NumberField.RingOfIntegers K) K

/-- The solvable-group and Galois-correspondence construction of the cyclic
intermediate extension in Lemma VII.4.5. -/
theorem cyclicSubextensionBridge :
    CyclicSubextensionBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _ hdegree
  let G := Gal(L/K)
  have hG : Nontrivial G := by
    by_contra htrivial
    letI : Subsingleton G := not_nontrivial_iff_subsingleton.mp htrivial
    apply hdegree
    rw [← IsGalois.card_aut_eq_finrank]
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, ⟨1⟩⟩
  letI : Nontrivial G := hG
  obtain ⟨H, hHtop, hnormal, hcyclic⟩ :=
    proper_normal_cyclic (G := G)
  letI : H.Normal := hnormal
  let E := IntermediateField.fixedField H
  let eQ : G ⧸ H ≃* Gal(E/K) :=
    IsGalois.normalAutEquivQuotient H
  have hcyclicE : IsCyclic Gal(E/K) := eQ.isCyclic.mp hcyclic
  have hdegreeE : 1 < Module.finrank K E := by
    rw [← IsGalois.card_aut_eq_finrank]
    rw [← Nat.card_congr eQ.toEquiv]
    letI : Nontrivial (G ⧸ H) :=
      QuotientGroup.nontrivial_iff.mpr hHtop
    exact Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  exact ⟨{
    E := E
    fieldE := inferInstance
    numberFieldE := inferInstance
    algebraKE := inferInstance
    algebraEL := inferInstance
    scalarTower := inferInstance
    finiteDimensionalKE := inferInstance
    finiteDimensionalEL := inferInstance
    isGaloisKE := inferInstance
    isGaloisEL := inferInstance
    isCyclicKE := hcyclicE
    one_lt_finrank := hdegreeE }⟩

/-- After discharging the solvable-group step, Lemma VII.4.5 retains only
the earlier openness/first-inequality results and concrete norm
transitivity. -/
theorem cyclic_subextension_transitivity
    (hopen : ∀ (K L : Type u) [Field K] [Field L]
      [NumberField K] [NumberField L] [Algebra K L]
      [FiniteDimensional K L],
      IdeleSubgroupOpen (K := K) (L := L))
    (hfirst : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          Module.finrank K L ≤
            (principalIdeles (NumberField.RingOfIntegers K) K ⊔
              ideleNormSubgroup (K := K) (L := L)).index))
    (htrans : SubextensionTransitivityBridge.{u}) :
    (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ D : Subgroup (IK K),
            D ≤ ideleNormSubgroup (K := K) (L := L) →
            Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
              Subgroup (IK K)) : Set (IK K)) →
            Module.finrank K L = 1) :=
  subextension_previous_results hopen hfirst
    cyclicSubextensionBridge htrans

/-- The concrete idèle norm construction supplies the transitivity input
used in Lemma VII.4.5. -/
theorem subextensionTransitivityBridge :
    SubextensionTransitivityBridge.{u} := by
  intro K E L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  exact ideleNorm_trans (K := K) (E := E) (L := L)

/-- Lemma VII.4.5 now depends only on the earlier openness and first-inequality
results. -/
theorem previous_results_only
    (hopen : ∀ (K L : Type u) [Field K] [Field L]
      [NumberField K] [NumberField L] [Algebra K L]
      [FiniteDimensional K L],
      IdeleSubgroupOpen (K := K) (L := L))
    (hfirst : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsCyclic Gal(L/K)],
          Module.finrank K L ≤
            (principalIdeles (NumberField.RingOfIntegers K) K ⊔
              ideleNormSubgroup (K := K) (L := L)).index)) :
    (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ D : Subgroup (IK K),
            D ≤ ideleNormSubgroup (K := K) (L := L) →
            Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
              Subgroup (IK K)) : Set (IK K)) →
            Module.finrank K L = 1) :=
  cyclic_subextension_transitivity hopen hfirst
    subextensionTransitivityBridge

end

end Submission.CField.NIndex

import Submission.ClassField.HasseNorm.LocalComparison
import Submission.ClassField.IdeleCohomology.CompletionProductAction
import Submission.ClassField.Reciprocity.CompletionPlaceConjugation
import Submission.ClassField.BrauerLocalization.InfiniteTateZero

/-!
# Archimedean Artin maps needed by Lemma VII.8.4

This file isolates the archimedean norm-residue map and its independence
from the chosen upper infinite place.  Keeping this small API separate
prevents VII.8.4 from importing the substantially larger full source file
for Lemma V.5.1.
-/

namespace Submission.CField.RExist

open AbsoluteValue NumberField
open Submission.NumberTheory.Milne
open Submission.CField.LFTheory
open Submission.CField.BGroups
open Submission.CField.Ideles
open Submission.CField.Recip
open Submission.CField.ICohomo
open Submission.CField.GWang
open Submission.CField.HNorm
open Submission.CField.BLoc

noncomputable section

universe u

/-- The archimedean norm quotient is canonically equivalent to the
decomposition group. -/
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
      Additive (relativeBrauerGroup v.1.Completion w.1.1.Completion) :=
    (hasseGlobal2
      v.1.Completion w.1.1.Completion hlocalCyclic).trans
        (relativeBrauer2
          v.1.Completion w.1.1.Completion).symm
  have hcard : Nat.card
      (v.1.Completionˣ ⧸ normSubgroup v.1.Completion w.1.1.Completion) =
      Nat.card D := by
    calc
      _ = Nat.card (relativeBrauerGroup
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

/-- Include an archimedean norm-residue equivalence into the global Galois
group. -/
def quotientEquivGlobal
    {U G : Type*} [CommGroup U] [Group G]
    (N : Subgroup U) (D : Subgroup G) (e : (U ⧸ N) ≃* D) : U →* G :=
  D.subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' N))

private theorem quotient_equiv_global
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

/-- The canonical archimedean local Artin map with global target. -/
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
-- Transporting norm ranges between conjugate completions unfolds their algebra structures.
set_option synthInstance.maxHeartbeats 500000 in
-- The two transported completion algebras require deeper instance search.
private theorem infinite_place_range
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
        congrArg (fun y ↦ sigma⁻¹ • y) hsigma.symm
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

private theorem infinite_place_decomposition
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
-- Choice-independence combines norm transport with decomposition-group conjugacy.
set_option synthInstance.maxHeartbeats 1000000 in
-- The decomposition subgroups and completion actions form a deep instance tower.
/-- The archimedean Artin map is independent of the chosen upper place. -/
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

end

end Submission.CField.RExist

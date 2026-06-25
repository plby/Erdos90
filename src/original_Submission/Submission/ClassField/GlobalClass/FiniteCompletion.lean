import Submission.ClassField.GlobalClass.LocalDegreeLCM
import Submission.ClassField.GlobalClass.BrauerSequenceStatements
import Submission.NumberTheory.Galois.PlaceCompletionDegree
import Submission.ClassField.IdeleCohomology.CompletionProductAction
import Submission.ClassField.IdeleCohomology.ArchimedeanProduct
import Submission.ClassField.Ideles.IdeleNorm
import Submission.ClassField.NormIndex.NumberFieldElement
import Submission.ClassField.NormIndex.CompletionPlaceBridge
import Submission.NumberTheory.Ramification.RamificationDiscriminant

/-! # Chapter VIII, Section 4, Lemma 4.1

For a cyclic number-field extension, its global degree is the least common
multiple of its finite-place completion degrees.  The only arithmetic input
isolated here is an actual family of Frobenius elements which generates the
Galois group; the lcm argument and divisibility of every local degree are
proved.
-/

namespace Submission.CField.GClass

open AbsoluteValue IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open scoped Pointwise TensorProduct

noncomputable section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

private abbrev IK (K : Type u) [Field K] [NumberField K] :=
  IdeleGroup (NumberField.RingOfIntegers K) K

private abbrev FiniteCompletionOK
    (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

local instance ringOfIntegersGaloisAction
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    MulSemiringAction Gal(L/K) (FiniteCompletionOK L) :=
  IsIntegralClosure.MulSemiringAction (FiniteCompletionOK K) K L (FiniteCompletionOK L)

local instance ringOfIntegersGaloisAction_smulCommClass
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    SMulCommClass Gal(L/K) (FiniteCompletionOK K) (FiniteCompletionOK L) where
  smul_comm sigma a b := by
    apply Subtype.ext
    have hG (x : FiniteCompletionOK L) :
        ((sigma • x : FiniteCompletionOK L) : L) = sigma (x : L) :=
      algebraMap.coe_smul' (B := FiniteCompletionOK L) (C := L) sigma x
    have hA (x : FiniteCompletionOK L) :
        ((a • x : FiniteCompletionOK L) : L) = (a : K) • (x : L) :=
      algebraMap.coe_smul (A := FiniteCompletionOK K) (B := FiniteCompletionOK L)
        (C := L) a x
    calc
      ((sigma • (a • b) : FiniteCompletionOK L) : L) =
          sigma (((a • b : FiniteCompletionOK L) : L)) := hG (a • b)
      _ = sigma ((a : K) • (b : L)) := congrArg sigma (hA b)
      _ = (a : K) • sigma (b : L) := smul_comm sigma (a : K) (b : L)
      _ = (a : K) • ((sigma • b : FiniteCompletionOK L) : L) :=
        congrArg (fun y : L ↦ (a : K) • y) (hG b).symm
      _ = ((a • (sigma • b) : FiniteCompletionOK L) : L) := (hA (sigma • b)).symm

local instance ringOfIntegersIsInvariant
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    Algebra.IsInvariant (FiniteCompletionOK K) (FiniteCompletionOK L) Gal(L/K) :=
  Algebra.isInvariant_of_isGalois (A := FiniteCompletionOK K) (K := K)
    (L := L) (B := FiniteCompletionOK L)

local instance ringOfIntegersIsGaloisGroup
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] :
    IsGaloisGroup Gal(L/K) (FiniteCompletionOK K) (FiniteCompletionOK L) :=
  IsGaloisGroup.of_isFractionRing (G := Gal(L/K))
    (A := FiniteCompletionOK K) (B := FiniteCompletionOK L) (K := K) (L := L)

/-- A finite prime of `K` together with a completion of `L` above it. -/
abbrev FiniteCompletion
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :=
  Σ P : HeightOneSpectrum (NumberField.RingOfIntegers K),
    CompletionPlacesAbove (L := L) (FinitePlace.mk P).val

/-- The actual degree of one completed extension `L_w/K_v`. -/
noncomputable def finiteCompletionDegree
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (v : FiniteCompletion K L) : ℕ := by
  letI : Algebra (FinitePlace.mk v.1).val.Completion v.2.1.Completion :=
    (completionLies (FinitePlace.mk v.1).val v.2.1 v.2.2).toAlgebra
  exact Module.finrank (FinitePlace.mk v.1).val.Completion v.2.1.Completion

set_option synthInstance.maxHeartbeats 500000 in
-- Completion algebra structures and the transitive place action are dependent.
/-- In a finite Galois extension, all completions above one finite place have
the same degree. -/
theorem finite_completion_degree
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (w z : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val) :
    finiteCompletionDegree (K := K) (L := L) ⟨P, w⟩ =
      finiteCompletionDegree (K := K) (L := L) ⟨P, z⟩ := by
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  letI : Finite (CompletionPlacesAbove (L := L) v) :=
    absolute_extensions_separable v
  letI : Nonempty (CompletionPlacesAbove (L := L) v) :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  letI (q : CompletionPlacesAbove (L := L) v) :
      Algebra v.Completion q.1.Completion :=
    (completionLies v q.1 q.2).toAlgebra
  obtain ⟨sigma, hsigma⟩ :=
    MulAction.exists_smul_eq Gal(L/K) z w
  have hz : sigma⁻¹ • w = z := by
    calc
      sigma⁻¹ • w = sigma⁻¹ • (sigma • z) :=
        congrArg (fun y => sigma⁻¹ • y) hsigma.symm
      _ = z := inv_smul_smul sigma z
  subst z
  change Module.finrank v.Completion w.1.Completion =
    Module.finrank v.Completion (sigma⁻¹ • w).1.Completion
  exact (completionTransportAlg v sigma w).toLinearEquiv.finrank_eq.symm

/-- A place of `K`, finite or infinite, together with a completion of `L`
above it. -/
abbrev Completion
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :=
  FiniteCompletion K L ⊕
    (Σ v : InfinitePlace K, InfinitePlacesAbove (K := K) (L := L) v)

/-- The actual local degree `[L_w : K_v]` at an arbitrary place. -/
noncomputable def completionDegree
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (v : Completion K L) : ℕ := by
  cases v with
  | inl v => exact finiteCompletionDegree v
  | inr v =>
      letI : Algebra v.1.1.Completion v.2.1.1.Completion :=
        (completionLies v.1.1 v.2.1.1
          (infinite_lies_comap v.1 v.2.1 v.2.2)).toAlgebra
      letI : Module.Finite v.1.1.Completion v.2.1.1.Completion :=
        infinite_completion_module (K := K) (L := L) v.1 v.2
      exact Module.finrank v.1.1.Completion v.2.1.1.Completion

/-- The narrow Artin/Frobenius input from the printed proof.  A generating
family of Frobenius elements is realized by actual finite primes and
completions, and each Frobenius order is the corresponding local degree.

The index type is deliberately arbitrary: Proposition VII.4.7 supplies the
family of unramified primes outside an exceptional set.  Requiring the
Frobenius map to be surjective would be strictly stronger than the printed
Artin-map argument. -/
structure FFam
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] where
  index : Type u
  prime : index → HeightOneSpectrum (NumberField.RingOfIntegers K)
  upper : ∀ i : index,
    CompletionPlacesAbove (L := L) (FinitePlace.mk (prime i)).val
  frobenius : index → Gal(L/K)
  frobenius_generates : Subgroup.closure (Set.range frobenius) = ⊤
  local_degree_order : ∀ i : index,
    finiteCompletionDegree
      (K := K) (L := L) ⟨prime i, upper i⟩ = orderOf (frobenius i)

def ArtinFrobeniusBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)],
    Nonempty (FFam K L)

/-- The finite exceptional-set input needed to apply Proposition VII.4.7.
This is standard discriminant/ramification finiteness and contains no Artin
or Frobenius conclusion. -/
def RamifiedSetBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L],
    ∃ T : Finset (FinitePrime L),
      NIndex.ContainsRamifiedPrimes (K := K) (L := L) T

/-- The ramified upper finite primes form a finite exceptional set. -/
theorem ramifiedSetBridge :
    RamifiedSetBridge.{u} := by
  classical
  intro K L _ _ _ _ _ _ _
  let R := NumberField.RingOfIntegers K
  let S := NumberField.RingOfIntegers L
  let ramified : Set (FinitePrime L) :=
    {Q | ¬Algebra.IsUnramifiedAt R Q.asIdeal}
  let differentPrimes : Set (Ideal S) :=
    {Q | Q.IsPrime ∧ Q ∣ differentIdeal R S}
  have hdifferent : differentPrimes.Finite :=
    set_dvd_different R S
  have hinjective : Function.Injective
      (fun Q : FinitePrime L ↦ Q.asIdeal) := by
    intro P Q hPQ
    exact HeightOneSpectrum.ext_iff.mpr hPQ
  have hramified : ramified.Finite := by
    apply (Set.Finite.preimage hinjective.injOn hdifferent).subset
    intro Q hQ
    change Q.asIdeal ∈ differentPrimes
    refine ⟨Q.isPrime, ?_⟩
    let p := Q.under R
    letI : Q.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
    apply (ramifies_dvd_different R S Q.asIdeal Q.ne_bot).mp
    intro hramificationIdx
    exact hQ ((unramified_ramification_idx
      p.asIdeal Q.asIdeal Q.ne_bot).2 hramificationIdx)
  refine ⟨hramified.toFinset, ?_⟩
  intro Q hQ
  by_contra hQramified
  apply hQ
  rw [Set.Finite.mem_toFinset]
  exact hQramified

/-- The remaining local arithmetic identity: at an unramified upper prime,
choose a normalized completion above its contraction whose degree is the
order of the actual arithmetic Frobenius. -/
def UnramifiedFrobeniusBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (Q : FinitePrime L),
    Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q.asIdeal →
      ∃ w : CompletionPlacesAbove (L := L)
          (FinitePlace.mk (Q.under (NumberField.RingOfIntegers K))).val,
        finiteCompletionDegree (K := K) (L := L)
            ⟨Q.under (NumberField.RingOfIntegers K), w⟩ =
          orderOf
            (NIndex.numberFrobeniusElement (K := K) Q)

set_option synthInstance.maxHeartbeats 500000 in
-- The centered completion, decomposition group, and residue extension are dependent.
set_option maxHeartbeats 3000000 in
/-- At an unramified upper prime, choose its centered normalized completion.
Its degree is the order of the actual arithmetic Frobenius. -/
theorem unramifiedFrobeniusBridge :
    UnramifiedFrobeniusBridge.{u} := by
  classical
  intro K L _ _ _ _ _ _ _ Q hQ
  letI : MulSemiringAction Gal(L/K) (FiniteCompletionOK L) :=
    IsIntegralClosure.MulSemiringAction (FiniteCompletionOK K) K L (FiniteCompletionOK L)
  letI : Algebra.IsUnramifiedAt (FiniteCompletionOK K) Q.asIdeal := hQ
  let P := Q.under (FiniteCompletionOK K)
  let factor := NIndex.upperPrimeFactor
    (K := K) (L := L) Q
  let w := NIndex.upperCompletionPlace
    (K := K) (L := L) P factor
  refine ⟨w, ?_⟩
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist P
  let hw := absolute_extension_nontrivial v w
  let hwna := absolute_extension_nonarchimedean v w
  have hcenter :
      nonarchimedeanHeightSpectrum w.1 hw hwna = Q := by
    calc
      nonarchimedeanHeightSpectrum w.1 hw hwna =
          upperPrime (K := K) (L := L) P factor :=
        NIndex.model_center_upper
          (K := K) (L := L) P factor
      _ = Q := NIndex.upper_prime_factor
        (K := K) (L := L) Q
  have hdecomposition :
      absoluteValueDecomposition v w.1 =
        MulAction.stabilizer Gal(L/K) Q.asIdeal := by
    rw [← centered_stabilizer_decomposition v w.1 hw hwna,
      hcenter]
  letI : Q.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
  letI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Q.asIdeal.IsMaximal := Q.isMaximal
  letI : Field ((FiniteCompletionOK K) ⧸ P.asIdeal) :=
    Ideal.Quotient.field P.asIdeal
  letI : Field ((FiniteCompletionOK L) ⧸ Q.asIdeal) :=
    Ideal.Quotient.field Q.asIdeal
  letI : Finite ((FiniteCompletionOK K) ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  letI : Finite ((FiniteCompletionOK L) ⧸ Q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient Q.ne_bot
  letI : Algebra.IsSeparable
      ((FiniteCompletionOK K) ⧸ P.asIdeal)
      ((FiniteCompletionOK L) ⧸ Q.asIdeal) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hstabilizer :
      Nat.card (MulAction.stabilizer Gal(L/K) Q.asIdeal) =
        P.asIdeal.inertiaDeg Q.asIdeal := by
    calc
      Nat.card (MulAction.stabilizer Gal(L/K) Q.asIdeal) =
          Nat.card (Q.asIdeal.inertia Gal(L/K)) *
            Module.finrank
              ((FiniteCompletionOK K) ⧸ P.asIdeal) ((FiniteCompletionOK L) ⧸ Q.asIdeal) :=
        Ideal.card_stabilizer_eq_card_inertia_mul_finrank
          (G := Gal(L/K)) P.asIdeal Q.asIdeal
      _ = Module.finrank
            ((FiniteCompletionOK K) ⧸ P.asIdeal) ((FiniteCompletionOK L) ⧸ Q.asIdeal) := by
        rw [inertia_bot_unramified
          (R := FiniteCompletionOK K) (G := Gal(L/K)) Q.asIdeal]
        simp
      _ = P.asIdeal.inertiaDeg Q.asIdeal :=
        (Ideal.inertiaDeg_algebraMap P.asIdeal Q.asIdeal).symm
  calc
    finiteCompletionDegree (K := K) (L := L) ⟨P, w⟩ =
        Nat.card (absoluteValueDecomposition v w.1) := by
      rw [finiteCompletionDegree,
        finrank_decomposition_card]
    _ = Nat.card (MulAction.stabilizer Gal(L/K) Q.asIdeal) := by
      rw [hdecomposition]
    _ = P.asIdeal.inertiaDeg Q.asIdeal := hstabilizer
    _ = orderOf
        (NIndex.numberFrobeniusElement (K := K) Q) := by
      rw [NIndex.numberFrobeniusElement]
      exact (frob_inertia_deg
        (R := FiniteCompletionOK K) (G := Gal(L/K)) Q.asIdeal).symm

/-- Proposition VII.4.7, ramification finiteness, and the unramified local
degree formula construct precisely the Frobenius family used by Lemma
VIII.4.1. -/
theorem artin_bridge_components
    (h47 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ T : Finset (FinitePrime L),
            NIndex.ContainsRamifiedPrimes (K := K) (L := L) T →
              NIndex.frobeniusGeneratedSubgroup (K := K) (L := L) T = ⊤))
    (hramified : RamifiedSetBridge.{u})
    (hdegree : UnramifiedFrobeniusBridge.{u}) :
    ArtinFrobeniusBridge.{u} := by
  classical
  intro K L _ _ _ _ _ _ _ _
  obtain ⟨T, hT⟩ := hramified K L
  let ι := {Q : FinitePrime L // Q ∉ T}
  let prime : ι → HeightOneSpectrum (NumberField.RingOfIntegers K) :=
    fun Q ↦ Q.1.under (NumberField.RingOfIntegers K)
  have hunramified (Q : ι) :
      Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) Q.1.asIdeal :=
    hT Q.1 Q.2
  let upper : ∀ Q : ι,
      CompletionPlacesAbove (L := L) (FinitePlace.mk (prime Q)).val :=
    fun Q ↦ Classical.choose (hdegree K L Q.1 (hunramified Q))
  let frobenius : ι → Gal(L/K) :=
    fun Q ↦ NIndex.numberFrobeniusElement (K := K) Q.1
  have hrange : Set.range frobenius =
      NIndex.frobeniusElementsOutside (K := K) (L := L) T := by
    ext sigma
    constructor
    · rintro ⟨Q, rfl⟩
      exact ⟨Q.1, Q.2, rfl⟩
    · rintro ⟨Q, hQT, hQ⟩
      exact ⟨⟨Q, hQT⟩, hQ⟩
  have hgenerate : Subgroup.closure (Set.range frobenius) = ⊤ := by
    rw [hrange]
    exact h47 K L T hT
  refine ⟨{
    index := ι
    prime := prime
    upper := upper
    frobenius := frobenius
    frobenius_generates := hgenerate
    local_degree_order := ?_ }⟩
  intro Q
  exact Classical.choose_spec (hdegree K L Q.1 (hunramified Q))

/-- Proposition VII.4.7 is the only remaining input to the Artin/Frobenius
bridge: ramification finiteness and the unramified completion-degree formula
are unconditional. -/
theorem artin_bridge_data
    (h47 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ T : Finset (FinitePrime L),
            NIndex.ContainsRamifiedPrimes (K := K) (L := L) T →
              NIndex.frobeniusGeneratedSubgroup (K := K) (L := L) T = ⊤)) :
    ArtinFrobeniusBridge.{u} :=
  artin_bridge_components
    h47 ramifiedSetBridge
      unramifiedFrobeniusBridge

/-- Proposition VII.4.6 supplies the Frobenius family after the fixed-field
proof of Proposition VII.4.7. -/
theorem artin_frobenius_bridge
    (h46 : NIndex.NontrivialNonsplitPrimes.{u}) :
    ArtinFrobeniusBridge.{u} :=
  artin_bridge_data
    (NIndex.numberElementStatement h46)

/-- The Artin/Frobenius bridge now needs only Lemma VII.4.5 and split-away
idèle-norm assembly from the VII.4.6 route. -/
theorem artin_split_away
    (h45 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ D : Subgroup (IK K),
            D ≤ ideleNormSubgroup (K := K) (L := L) →
            Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
              Subgroup (IK K)) : Set (IK K)) →
            Module.finrank K L = 1))
    (hnorm : NIndex.SplitAwayBridge.{u}) :
    ArtinFrobeniusBridge.{u} :=
  artin_bridge_data
    (NIndex.statement_split_away
      h45 hnorm)

/-- The Artin/Frobenius bridge now depends only on Lemma VII.4.5. -/
theorem artin_away_only
    (h45 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ D : Subgroup (IK K),
            D ≤ ideleNormSubgroup (K := K) (L := L) →
            Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
              Subgroup (IK K)) : Set (IK K)) →
            Module.finrank K L = 1)) :
    ArtinFrobeniusBridge.{u} :=
  artin_bridge_data
    (NIndex.number_statement_only h45)

/-- The global degree divides every common multiple of the selected local
degrees.  This is the closure-generation form of the lcm argument. -/
theorem FFam.globaldegree_dvdlocal_degreesdvd
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (data : FFam K L)
    (m : ℕ)
    (hm : ∀ i : data.index,
      finiteCompletionDegree
        (K := K) (L := L) ⟨data.prime i, data.upper i⟩ ∣ m) :
    Module.finrank K L ∣ m := by
  rw [← IsGalois.card_aut_eq_finrank K L]
  apply card_dvd_top
    data.frobenius data.frobenius_generates m
  intro i
  rw [← data.local_degree_order]
  exact hm i

/-- Every finite completion degree divides the global degree. -/
theorem degree_dvd_global
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : FiniteCompletion K L) :
    finiteCompletionDegree (K := K) (L := L) v ∣ Module.finrank K L := by
  rw [finiteCompletionDegree,
    finrank_decomposition_card]
  rw [← IsGalois.card_aut_eq_finrank K L]
  exact Subgroup.card_subgroup_dvd_card _

set_option synthInstance.maxHeartbeats 500000 in
-- Archimedean completion algebras are dependent on the chosen upper place.
set_option maxHeartbeats 3000000 in
/-- Every archimedean completion degree divides the global degree.  The
proof uses the product decomposition after base change to `K_v`; Galois
conjugation identifies all factors above `v`, so any one factor degree
divides their sum, which is `[L:K]`. -/
theorem infinite_dvd_global
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : Σ place : InfinitePlace K,
      InfinitePlacesAbove (K := K) (L := L) place) :
    completionDegree (K := K) (L := L) (.inr v) ∣
      Module.finrank K L := by
  let F := v.1.1.Completion
  let W := InfinitePlacesAbove (K := K) (L := L) v.1
  letI : Fintype W := Fintype.ofFinite W
  letI (z : W) : Algebra F z.1.1.Completion :=
    (completionLies v.1.1 z.1.1
      (infinite_lies_comap v.1 z.1 z.2)).toAlgebra
  letI (z : W) : Module.Finite F z.1.1.Completion :=
    infinite_completion_module (K := K) (L := L) v.1 z
  let e := infiniteTensorCompletions
    (K := K) (L := L) v.1
  have hsum :
      (∑ z : W, Module.finrank F z.1.1.Completion) = Module.finrank K L := by
    calc
      (∑ z : W, Module.finrank F z.1.1.Completion) =
          Module.finrank F (∀ z : W, z.1.1.Completion) :=
        (Module.finrank_pi_fintype (R := F)
          (M := fun z : W ↦ z.1.1.Completion)).symm
      _ = Module.finrank F (L ⊗[K] F) := e.toLinearEquiv.finrank_eq.symm
      _ = Module.finrank F (F ⊗[K] L) :=
        (Algebra.TensorProduct.commRight K F L).toLinearEquiv.finrank_eq.symm
      _ = Module.finrank K L := Module.finrank_baseChange
  letI := placesAboveAction (K := K) (L := L) v.1
  have hall (z : W) :
      Module.finrank F z.1.1.Completion =
        Module.finrank F v.2.1.1.Completion := by
    obtain ⟨sigma, hsigmaVal⟩ :=
      InfinitePlace.exists_smul_eq_of_comap_eq
        (z.2.trans v.2.2.symm)
    have hsigma : sigma • z = v.2 := by
      apply Subtype.ext
      change infinitePlaceAction sigma z.1 = v.2.1
      apply Subtype.ext
      rw [infinite_action_val]
      exact congrArg (fun w : InfinitePlace L ↦ w.1) hsigmaVal
    have hz : sigma⁻¹ • v.2 = z := by
      calc
        sigma⁻¹ • v.2 = sigma⁻¹ • (sigma • z) :=
          congrArg (fun y : W ↦ sigma⁻¹ • y) hsigma.symm
        _ = z := inv_smul_smul sigma z
    let et :
        InfiniteFamilyAbove v.1 (sigma⁻¹ • v.2) ≃ₐ[F]
          InfiniteFamilyAbove v.1 v.2 :=
      { infiniteFamilyTransport v.1 sigma v.2 with
        commutes' := infinite_transport_base v.1 sigma v.2 }
    rw [← hz]
    exact et.toLinearEquiv.finrank_eq
  change Module.finrank F v.2.1.1.Completion ∣ Module.finrank K L
  refine ⟨Fintype.card W, ?_⟩
  calc
    Module.finrank K L = ∑ z : W, Module.finrank F z.1.1.Completion := hsum.symm
    _ = ∑ _z : W, Module.finrank F v.2.1.1.Completion := by
      apply Finset.sum_congr rfl
      intro z hz
      exact hall z
    _ = Fintype.card W * Module.finrank F v.2.1.1.Completion := by simp
    _ = Module.finrank F v.2.1.1.Completion * Fintype.card W := mul_comm _ _

/-- Every finite or infinite completion degree divides the global degree. -/
theorem completion_dvd_global
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : Completion K L) :
    completionDegree (K := K) (L := L) v ∣ Module.finrank K L := by
  cases v with
  | inl v => exact degree_dvd_global v
  | inr v => exact infinite_dvd_global v

set_option synthInstance.maxHeartbeats 500000 in
-- Completion-degree typeclass synthesis unfolds the dependent completion algebra.
theorem completion_degree_pos
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : FiniteCompletion K L) :
    0 < finiteCompletionDegree (K := K) (L := L) v := by
  rw [finiteCompletionDegree,
    finrank_decomposition_card]
  exact Nat.card_pos

set_option synthInstance.maxHeartbeats 500000 in
-- Completion-degree typeclass synthesis unfolds the dependent completion algebra.
theorem completionDegree_pos
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (v : Completion K L) :
    0 < completionDegree (K := K) (L := L) v := by
  cases v with
  | inl v => exact completion_degree_pos v
  | inr v =>
      letI : Algebra v.1.1.Completion v.2.1.1.Completion :=
        (completionLies v.1.1 v.2.1.1
          (infinite_lies_comap v.1 v.2.1 v.2.2)).toAlgebra
      letI : Module.Finite v.1.1.Completion v.2.1.1.Completion :=
        infinite_completion_module (K := K) (L := L) v.1 v.2
      change 0 < Module.finrank v.1.1.Completion v.2.1.1.Completion
      exact Module.finrank_pos

theorem completion_artin_frobenius
    (hArtin : ArtinFrobeniusBridge.{u}) :
    (∀ (K L : Type u) [Field K] [NumberField K]
          [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)],
          LocalLCM
            (completionDegree (K := K) (L := L))
            (Module.finrank K L)) := by
  intro K L _ _ _ _ _ _ _ _
  obtain ⟨data⟩ := hArtin K L
  refine ⟨Module.finrank_pos, ?_, ?_, ?_⟩
  · intro v
    exact completionDegree_pos v
  · intro v
    exact completion_dvd_global v
  · intro m hm
    exact data.globaldegree_dvdlocal_degreesdvd m fun i ↦
      hm (.inl ⟨data.prime i, data.upper i⟩)

/-- Lemma VIII.4.1 follows from the Frobenius-generation statement of
Proposition VII.4.7. -/
theorem global_lcm_generation
    (h47 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ T : Finset (FinitePrime L),
            NIndex.ContainsRamifiedPrimes (K := K) (L := L) T →
              NIndex.frobeniusGeneratedSubgroup (K := K) (L := L) T = ⊤)) :
    (∀ (K L : Type u) [Field K] [NumberField K]
          [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)],
          LocalLCM
            (completionDegree (K := K) (L := L))
            (Module.finrank K L)) :=
  completion_artin_frobenius
    (artin_bridge_data h47)

/-- Lemma VIII.4.1 follows already from Proposition VII.4.6: the intervening
fixed-field Frobenius-generation argument is now formalized. -/
theorem lcm_nonsplit_primes
    (h46 : NIndex.NontrivialNonsplitPrimes.{u}) :
    (∀ (K L : Type u) [Field K] [NumberField K]
          [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)],
          LocalLCM
            (completionDegree (K := K) (L := L))
            (Module.finrank K L)) :=
  completion_artin_frobenius
    (artin_frobenius_bridge h46)

/-- Lemma VIII.4.1 along the sharpened VII.4.6 dependency boundary. -/
theorem statement_away_norm
    (h45 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ D : Subgroup (IK K),
            D ≤ ideleNormSubgroup (K := K) (L := L) →
            Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
              Subgroup (IK K)) : Set (IK K)) →
            Module.finrank K L = 1))
    (hnorm : NIndex.SplitAwayBridge.{u}) :
    (∀ (K L : Type u) [Field K] [NumberField K]
          [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)],
          LocalLCM
            (completionDegree (K := K) (L := L))
            (Module.finrank K L)) :=
  completion_artin_frobenius
    (artin_split_away h45 hnorm)

/-- Lemma VIII.4.1 along the final VII.4 dependency boundary. -/
theorem completion_statement_only
    (h45 : (∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
          [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
          [IsSolvable Gal(L/K)],
          ∀ D : Subgroup (IK K),
            D ≤ ideleNormSubgroup (K := K) (L := L) →
            Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
              Subgroup (IK K)) : Set (IK K)) →
            Module.finrank K L = 1)) :
    (∀ (K L : Type u) [Field K] [NumberField K]
          [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)],
          LocalLCM
            (completionDegree (K := K) (L := L))
            (Module.finrank K L)) :=
  completion_artin_frobenius
    (artin_away_only h45)

end

end Submission.CField.GClass

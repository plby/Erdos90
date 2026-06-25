import Towers.ClassField.BrauerLocalization.FiniteCyclicSequence
import Towers.ClassField.CrossedProducts.IsMulCoboundary
import Towers.ClassField.LocalBrauer.FiniteRelativeCardinality
import Towers.ClassField.LocalClass.FiniteRelativeCardinality
import Towers.ClassField.LocalClass.NatCardFinrank
import Towers.ClassField.GlobalClass.FiniteCompletion
import Towers.ClassField.BrauerLocalization.CokernelAssembly
import Towers.ClassField.CyclicIdeles.AlgebraicIdeleCohomology

/-!
# The cohomological top row of the finite cyclic relative Brauer sequence

This file constructs the obstruction group and the top row in the diagram
preceding Theorem VIII.4.2.  The obstruction group is the literal
`H²(Gal(L/K), C_L)` arising from the resized idèle-class short exact
sequence.  The local-to-obstruction map is the `H²` map induced by
`I_L → C_L`, transported through the already-proved idèle decomposition
and local crossed-product equivalences.

The long exact sequence proves exactness of this top row.  Theorem VII.5.1
supplies finiteness and the cardinality bound on the obstruction group.  The
only data still needed for the finite cyclic cardinality argument is thus the
bottom invariant map, its factorization through the obstruction image, and
surjectivity of that induced map.
-/

namespace Towers.CField.BLoc

open CategoryTheory Representation groupCohomology
open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LClass
open Towers.CField.LFTheory
open Towers.CField.LRecip
open Towers.CField.BGroups
open Towers.CField.CProduca
open Towers.CField.LBrauer
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.CIdeles
open Towers.CField.CBrauer
open Towers.CField.RExist
open Towers.CField.HNorm
open Towers.CField.GClass

noncomputable section

universe u v

/-- The current explicit statement of Proposition VII.4.7. -/
private abbrev FrobeniusGeneration : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsSolvable Gal(L/K)],
    ∀ T : Finset (FinitePrime L),
      NIndex.ContainsRamifiedPrimes (K := K) (L := L) T →
        NIndex.frobeniusGeneratedSubgroup (K := K) (L := L) T = ⊤

/-- The current explicit statement of the first idèle-index inequality. -/
private abbrev FirstInequality : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsCyclic Gal(L/K)],
    Module.finrank K L ≤
      (principalIdeles (NumberField.RingOfIntegers K) K ⊔
        ideleNormSubgroup (K := K) (L := L)).index

/-- Exactness is preserved when the first and middle terms are replaced by
additively equivalent presentations. -/
theorem exact_transport_add
    {A X B Y C : Type*}
    [AddCommGroup A] [AddCommGroup X] [AddCommGroup B]
    [AddCommGroup Y] [AddCommGroup C]
    (eA : A ≃+ X) (eB : B ≃+ Y)
    (f : X →+ B) (g : B →+ C)
    (hfg : Function.Exact f g) :
    Function.Exact
      (eB.toAddMonoidHom.comp (f.comp eA.toAddMonoidHom))
      (g.comp eB.symm.toAddMonoidHom) := by
  intro y
  constructor
  · intro hy
    obtain ⟨x, hx⟩ := (hfg (eB.symm y)).mp hy
    refine ⟨eA.symm x, ?_⟩
    change eB (f (eA (eA.symm x))) = y
    rw [eA.apply_symm_apply, hx, eB.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    change g (eB.symm (eB (f (eA a)))) = 0
    rw [eB.symm_apply_apply]
    exact (hfg (f (eA a))).mpr ⟨eA a, rfl⟩

variable (K L : Type u) [Field K] [NumberField K]
  [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- Spectral local-invariant base change at every chosen finite completion
of a finite Galois number-field extension. -/
def RelativeSpectralChange : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (completion : HasseCompletionData K L)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
    let v := (FinitePlace.mk P).val
    let w := hasseChosenPlace completion (.inl P)
    letI : Fact v.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
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
    letI : Algebra v.Completion w.1.Completion :=
      (completionLies v w.1 w.2).toAlgebra
    letI : FiniteDimensional v.Completion w.1.Completion :=
      Towers.NumberTheory.Milne.placeCompletionDimensional v w
    SpectralChangeFormula v.Completion w.1.Completion

set_option maxHeartbeats 4000000 in
-- Chosen completion algebras and local-field structures are deeply dependent.
/-- At a finite place, spectral local invariant base change and the global
divisibility of the completion degree prove the pointwise torsion field. -/
theorem cyclic_relative_torsion
    (hbaseChange : RelativeSpectralChange.{u})
    (completion : HasseCompletionData K L)
    (data : BData K)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (beta : Additive
      (localRelativeBrauer K L completion (.inl P))) :
    Module.finrank K L •
      data.placeInvariant.invariant (.inl P)
        (localBrauerInclusion
          K L completion (.inl P) beta) = 0 := by
  let v := (FinitePlace.mk P).val
  let w := hasseChosenPlace completion (.inl P)
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
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
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  have hlocal : Module.finrank v.Completion w.1.Completion •
      (carryBrauerInvariant v.Completion beta.toMul.1).toAdd = 0 :=
    nsmul_spectral_change
      v.Completion w.1.Completion (hbaseChange K L completion P)
        (Additive.ofMul beta.toMul.1) beta.toMul.2
  have hdegree : Module.finrank v.Completion w.1.Completion ∣
      Module.finrank K L := by
    simpa only [finiteCompletionDegree] using
      degree_dvd_global
        (K := K) (L := L) (⟨P, w⟩ : FiniteCompletion K L)
  obtain ⟨d, hd⟩ := hdegree
  rw [data.placeInvariant.finite_eq P]
  change Module.finrank K L •
    (carryBrauerInvariant v.Completion beta.toMul.1).toAdd = 0
  rw [hd, mul_nsmul, hlocal, nsmul_zero]

/-- Finite spectral base change plus the remaining archimedean assertion
give pointwise torsion at every number-field place. -/
theorem relative_torsion_infinite
    (hbaseChange : RelativeSpectralChange.{u})
    (completion : HasseCompletionData K L)
    (data : BData K)
    (hinfinite : ∀ (v : InfinitePlace K)
      (beta : Additive
        (localRelativeBrauer K L completion (.inr v))),
      Module.finrank K L •
        data.placeInvariant.invariant (.inr v)
          (localBrauerInclusion
            K L completion (.inr v) beta) = 0)
    (place : NumberFieldPlace K)
    (beta : Additive
      (localRelativeBrauer K L completion place)) :
    Module.finrank K L •
      data.placeInvariant.invariant place
        (localBrauerInclusion
          K L completion place beta) = 0 := by
  cases place with
  | inl P =>
      exact cyclic_relative_torsion
        K L hbaseChange completion data P beta
  | inr v => exact hinfinite v beta

/-- A relative Brauer class is killed by the local extension degree; hence
any additive invariant of its underlying Brauer class is killed by every
multiple of that degree. -/
theorem invariant_nsmul_dvd
    {k E : Type u} {A : Type v} [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [AddCommGroup A]
    (n : ℕ) (hdegree : Module.finrank k E ∣ n)
    (inv : Additive (BrauerGroup k) →+ A)
    (beta : Additive (relativeBrauerGroup k E)) :
    n • inv (MonoidHom.toAdditive (relativeBrauerGroup k E).subtype beta) = 0 := by
  have hbeta : Module.finrank k E • beta = 0 := by
    apply Additive.toMul.injective
    exact relative_brauer_extension k E beta.toMul
  have hlocal : Module.finrank k E •
      inv (MonoidHom.toAdditive (relativeBrauerGroup k E).subtype beta) = 0 := by
    change Module.finrank k E •
      inv (Additive.ofMul (beta.toMul : BrauerGroup k)) = 0
    rw [← map_nsmul]
    have hval := congrArg
      (fun z : Additive (relativeBrauerGroup k E) ↦
        Additive.ofMul (z.toMul.1 : BrauerGroup k)) hbeta
    exact (congrArg inv (by simpa using hval)).trans (map_zero inv)
  obtain ⟨d, rfl⟩ := hdegree
  rw [mul_nsmul, hlocal, nsmul_zero]

set_option maxHeartbeats 4000000 in
-- Both place branches install dependent chosen-completion algebra structures.
/-- Pointwise `[L:K]`-torsion of every chosen local relative invariant is
unconditional: Corollary IV.3.17 kills the relative Brauer class by the
local degree, and every local completion degree divides the global degree. -/
theorem relative_local_torsion
    (completion : HasseCompletionData K L)
    (data : BData K)
    (place : NumberFieldPlace K)
    (beta : Additive
      (localRelativeBrauer K L completion place)) :
    Module.finrank K L •
      data.placeInvariant.invariant place
        (localBrauerInclusion
          K L completion place beta) = 0 := by
  cases place with
  | inl P =>
      let v := (FinitePlace.mk P).val
      let w := hasseChosenPlace completion (.inl P)
      letI : Fact v.IsNontrivial :=
        ⟨absolute_value_nontrivial P⟩
      letI : IsUltrametricDist v.Completion :=
        placeUltrametricDist P
      letI : Algebra v.Completion w.1.Completion :=
        (completionLies v w.1 w.2).toAlgebra
      letI : FiniteDimensional v.Completion w.1.Completion :=
        Towers.NumberTheory.Milne.placeCompletionDimensional v w
      have hdegree : Module.finrank v.Completion w.1.Completion ∣
          Module.finrank K L := by
        simpa only [finiteCompletionDegree] using
          degree_dvd_global
            (K := K) (L := L) (⟨P, w⟩ : FiniteCompletion K L)
      simpa only [localBrauerInclusion,
        localRelativeBrauer, hasseAbsoluteValue,
        chosenCompletionExtension] using
        invariant_nsmul_dvd
          (Module.finrank K L) hdegree
          (data.placeInvariant.invariant (.inl P)) beta
  | inr v =>
      let w := completion.infiniteUpper v
      let hwv := infinite_lies_comap v w.1 w.2
      letI : Algebra v.1.Completion w.1.1.Completion :=
        (completionLies v.1 w.1.1 hwv).toAlgebra
      letI : FiniteDimensional v.1.Completion w.1.1.Completion :=
        infinite_completion_module (K := K) (L := L) v w
      have hdegree : Module.finrank v.1.Completion w.1.1.Completion ∣
          Module.finrank K L := by
        simpa only [completionDegree] using
          infinite_dvd_global
            (K := K) (L := L) ⟨v, w⟩
      simpa only [localBrauerInclusion,
        localRelativeBrauer, hasseAbsoluteValue,
        chosenCompletionExtension] using
        invariant_nsmul_dvd
          (Module.finrank K L) hdegree
          (data.placeInvariant.invariant (.inr v)) beta

/-- Milne's obstruction group `H²(L/K) = H²(Gal(L/K), C_L)`, in the
literal resized idèle-class representation used by the exact sequence. -/
abbrev finiteRelativeObstruction :=
  H2 (resizedShortComplex K L).X₃

set_option synthInstance.maxHeartbeats 300000 in
-- The local comparison is a dependent direct sum over chosen completions.
/-- The idèle `H²` term identified with the direct sum of the chosen local
relative Brauer groups. -/
noncomputable def cyclicRelativeLocal
    (completion : HasseCompletionData K L) :
    H2 (resizedShortComplex K L).X₂ ≃+
      CyclicRelativeSum K L completion :=
  (resizedHDecomposition
      (K := K) (L := L)).trans
    (directRelativeBrauer
      K L completion)

set_option synthInstance.maxHeartbeats 300000 in
-- The codomain is the dependent local relative-Brauer direct sum.
/-- The map from the local relative Brauer direct sum to
`H²(Gal(L/K), C_L)` induced by `I_L → C_L`. -/
noncomputable def relativeLocalObstruction
    (completion : HasseCompletionData K L) :
    CyclicRelativeSum K L completion →+
      finiteRelativeObstruction K L :=
  (groupCohomology.mapShortComplex₂
      (resizedShortComplex K L) 2).g.hom.toAddMonoidHom.comp
    (cyclicRelativeLocal
      K L completion).symm.toAddMonoidHom

/-- Exactness of the degree-two middle segment of the idèle-class long
exact sequence, before changing presentations. -/
theorem resized_row_exact :
    Function.Exact
      (groupCohomology.mapShortComplex₂
        (resizedShortComplex K L) 2).f.hom.toAddMonoidHom
      (groupCohomology.mapShortComplex₂
        (resizedShortComplex K L) 2).g.hom.toAddMonoidHom := by
  let X := resizedShortComplex K L
  let S := groupCohomology.mapShortComplex₂ X 2
  have hS : S.Exact := groupCohomology.mapShortComplex₂_exact
    (resized_short_exact K L) 2
  exact
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS

set_option maxHeartbeats 4000000 in
-- Unfolding the two composed equivalences is elaboration-intensive.
/-- The concrete relative Brauer localization and the concrete obstruction
map form the exact top row in Milne's finite-level diagram. -/
theorem top_row_exact
    (completion : HasseCompletionData K L) :
    Function.Exact
      (brauerCohomologicalLocalization K L completion)
      (relativeLocalObstruction K L completion) := by
  let eGlobal := relativeBrauerResized K L
  let eLocal := cyclicRelativeLocal K L completion
  have h := exact_transport_add eGlobal eLocal
    (groupCohomology.mapShortComplex₂
      (resizedShortComplex K L) 2).f.hom.toAddMonoidHom
    (groupCohomology.mapShortComplex₂
      (resizedShortComplex K L) 2).g.hom.toAddMonoidHom
    (resized_row_exact K L)
  simpa only [eGlobal, eLocal,
    cyclicRelativeLocal,
    relativeLocalObstruction,
    brauerCohomologicalLocalization,
    relativeH2,
    relativeResized2,
    AddEquiv.trans_apply,
    AddMonoidHom.coe_comp,
    Function.comp_apply,
    AddMonoidHom.comp_assoc] using h

/-- The representation isomorphism comparing the obstruction group with the
literal idèle-class `H²` used in Theorem VII.5.1. -/
noncomputable def cyclicRelativeObstruction :
    finiteRelativeObstruction K L ≃+
      H2 (ideleCohomologyRepresentation K L) :=
  ((groupCohomology.functor (ULift.{u} ℤ) Gal(L/K) 2).mapIso
    (resizedIdeleIso K L)).toLinearEquiv.toAddEquiv

/-- Theorem VII.5.1 makes the finite-level obstruction group finite. -/
theorem cyclic_relative_obstruction
    (h51 : IdeleCohomologyClaims.{u}) :
    Finite (finiteRelativeObstruction K L) := by
  letI : Finite (H2 (ideleCohomologyRepresentation K L)) :=
    (h51 K L).2.2.1
  exact Finite.of_equiv (H2 (ideleCohomologyRepresentation K L))
    (cyclicRelativeObstruction K L).symm.toEquiv

/-- Theorem VII.5.1 transports to the cardinality bound on the literal
obstruction group used by the top row. -/
theorem relative_obstruction_card
    (h51 : IdeleCohomologyClaims.{u}) :
    Nat.card (finiteRelativeObstruction K L) ≤
      Module.finrank K L := by
  have hdvd : Nat.card (H2 (ideleCohomologyRepresentation K L)) ∣
      Module.finrank K L := (h51 K L).2.2.2
  calc
    Nat.card (finiteRelativeObstruction K L) =
        Nat.card (H2 (ideleCohomologyRepresentation K L)) :=
      Nat.card_congr
        (cyclicRelativeObstruction K L).toEquiv
    _ ≤ Module.finrank K L :=
      Nat.le_of_dvd (Module.finrank_pos (R := K) (M := L)) hdvd

/-- A homomorphism whose kernel contains the kernel of `g` descends to the
range of `g`.  This is the first-isomorphism-theorem construction used for
Milne's induced map on `H²(L/K)'`. -/
noncomputable def monoidDescendRange
    {B C T : Type*} [AddCommGroup B] [AddCommGroup C] [AddCommGroup T]
    (g : B →+ C) (s : B →+ T) (hker : g.ker ≤ s.ker) :
    g.range →+ T :=
  (QuotientAddGroup.lift g.ker s hker).comp
    (QuotientAddGroup.quotientKerEquivRange g).symm.toAddMonoidHom

@[simp]
theorem monoid_descend_range
    {B C T : Type*} [AddCommGroup B] [AddCommGroup C] [AddCommGroup T]
    (g : B →+ C) (s : B →+ T) (hker : g.ker ≤ s.ker) (b : B) :
    monoidDescendRange g s hker
      ⟨g b, Set.mem_range_self b⟩ = s b := by
  change (QuotientAddGroup.lift g.ker s hker)
    ((QuotientAddGroup.quotientKerEquivRange g).symm
      ⟨g b, Set.mem_range_self b⟩) = s b
  have hquot :
      (QuotientAddGroup.quotientKerEquivRange g).symm
          ⟨g b, Set.mem_range_self b⟩ =
        QuotientAddGroup.mk' g.ker b := by
    apply (QuotientAddGroup.quotientKerEquivRange g).injective
    rw [(QuotientAddGroup.quotientKerEquivRange g).apply_symm_apply]
    rfl
  rw [hquot]
  exact QuotientAddGroup.lift_mk' g.ker hker b

/-- Exactness of `f,g` and vanishing of `s` on the range of `f` imply the
kernel containment needed to descend `s` to the range of `g`. -/
theorem ker_exact_comp
    {A B C T : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup T]
    (f : A →+ B) (g : B →+ C) (s : B →+ T)
    (hfg : Function.Exact f g) (hzero : ∀ a, s (f a) = 0) :
    g.ker ≤ s.ker := by
  intro b hb
  obtain ⟨a, rfl⟩ := (hfg b).mp (AddMonoidHom.mem_ker.mp hb)
  exact AddMonoidHom.mem_ker.mpr (hzero a)

/-- If `s` is surjective, then its descended map on the range of `g` is
surjective as well. -/
theorem monoid_descend_surjective
    {B C T : Type*} [AddCommGroup B] [AddCommGroup C] [AddCommGroup T]
    (g : B →+ C) (s : B →+ T) (hker : g.ker ≤ s.ker)
    (hs : Function.Surjective s) :
    Function.Surjective (monoidDescendRange g s hker) := by
  intro t
  obtain ⟨b, rfl⟩ := hs t
  exact ⟨⟨g b, Set.mem_range_self b⟩,
    monoid_descend_range g s hker b⟩

/-- Restrict the canonical local invariant of a local relative Brauer class
to the `[L:K]`-torsion subgroup, given the pointwise torsion assertion from
local invariant base change and local-degree divisibility. -/
noncomputable def cyclicRelativeInvariant
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K)
    (htorsion : ∀ (v : NumberFieldPlace K)
      (beta : Additive (localRelativeBrauer K L completion v)),
      Module.finrank K L •
        placeInvariant.invariant v
          (localBrauerInclusion K L completion v beta) = 0)
    (v : NumberFieldPlace K) :
    Additive (localRelativeBrauer K L completion v) →+
      localInvariantTorsion (Module.finrank K L) :=
  ((placeInvariant.invariant v).comp
    (localBrauerInclusion K L completion v)).codRestrict
      (localInvariantTorsion (Module.finrank K L)) (htorsion v)

set_option synthInstance.maxHeartbeats 300000 in
-- The source is the dependent local relative-Brauer direct sum.
/-- Sum the restricted local invariants into the global-degree torsion
subgroup. -/
noncomputable def relativeInvariantSum
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K)
    (htorsion : ∀ (v : NumberFieldPlace K)
      (beta : Additive (localRelativeBrauer K L completion v)),
      Module.finrank K L •
        placeInvariant.invariant v
          (localBrauerInclusion K L completion v beta) = 0) :
    CyclicRelativeSum K L completion →+
      localInvariantTorsion (Module.finrank K L) := by
  classical
  exact DirectSum.toAddMonoid
    (cyclicRelativeInvariant K L completion placeInvariant htorsion)

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent direct-sum family requires deeper instance synthesis.
set_option maxHeartbeats 4000000 in
-- Comparing the two dependent direct-sum homomorphisms is elaboration-heavy.
/-- Coercing the restricted invariant sum to `Q/Z` gives exactly the literal
sum of the supplied place invariants after inclusion into absolute local
Brauer groups. -/
theorem relative_invariant_coe
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K)
    (htorsion : ∀ (v : NumberFieldPlace K)
      (beta : Additive (localRelativeBrauer K L completion v)),
      Module.finrank K L •
        placeInvariant.invariant v
          (localBrauerInclusion K L completion v beta) = 0)
    (y : CyclicRelativeSum K L completion) :
    ((relativeInvariantSum K L completion placeInvariant htorsion y :
        localInvariantTorsion (Module.finrank K L)) : LocalInvariant) =
      placeInvariant.sum K
        (brauerDirectInclusion K L completion y) := by
  classical
  let left : CyclicRelativeSum K L completion →+ LocalInvariant :=
    (localInvariantTorsion (Module.finrank K L)).subtype.comp
      (relativeInvariantSum K L completion placeInvariant htorsion)
  let right : CyclicRelativeSum K L completion →+ LocalInvariant :=
    (placeInvariant.sum K).comp
      (brauerDirectInclusion K L completion)
  have hhom : left = right := by
    apply DirectSum.addHom_ext
    intro v beta
    simp [left, right, relativeInvariantSum,
      cyclicRelativeInvariant,
      PIData.sum,
      brauerDirectInclusion]
  exact DFunLike.congr_fun hhom y

/-- Inclusion between torsion subgroups of the local invariant group along
divisibility of their exponents. -/
noncomputable def torsionInclusionDvd
    (d n : ℕ) (hdn : d ∣ n) :
    localInvariantTorsion d →+ localInvariantTorsion n := by
  refine (localInvariantTorsion d).subtype.codRestrict
    (localInvariantTorsion n) fun x ↦ ?_
  obtain ⟨c, rfl⟩ := hdn
  change (d * c) • (x : LocalInvariant) = 0
  have hx : d • (x : LocalInvariant) = 0 := x.property
  calc
    (d * c) • (x : LocalInvariant) = c • (d • (x : LocalInvariant)) :=
      mul_nsmul (x : LocalInvariant) d c
    _ = c • 0 := congrArg (fun y : LocalInvariant ↦ c • y) hx
    _ = 0 := by simp

theorem torsion_inclusion_injective
    (d n : ℕ) (hdn : d ∣ n) :
    Function.Injective (torsionInclusionDvd d n hdn) := by
  intro x y hxy
  apply Subtype.ext
  change (x : LocalInvariant) = (y : LocalInvariant)
  have hval := congrArg
    (fun z : localInvariantTorsion n ↦ (z : LocalInvariant)) hxy
  exact hval

theorem invariant_torsion_card (n : ℕ) [NeZero n] :
    Nat.card (localInvariantTorsion n) = n := by
  calc
    Nat.card (localInvariantTorsion n) = Nat.card (ZMod n) :=
      Nat.card_congr (torsionZMod n).symm.toEquiv
    _ = n := Nat.card_zmod n

/-- Universe-polymorphic form of the cardinality-to-invariant equivalence.
The older Chapter III helper also continues into literal low-degree group
cohomology, whose Mathlib API forces universe zero; this local version uses
only the relative Brauer group and therefore works in the resized setting. -/
noncomputable def relativeBrauerCardinality
    (k E : Type u)
    [NontriviallyNormedField k] [IsUltrametricDist k] [ValuativeRel k]
    [IsNonarchimedeanLocalField k]
    [Valuation.Compatible (NormedField.valuation (K := k))]
    [Field E] [Algebra k E] [FiniteDimensional k E] [IsGalois k E]
    (hcard : Nat.card (relativeBrauerGroup k E) = Module.finrank k E) :
    relativeBrauerGroup k E ≃*
      Multiplicative (localInvariantTorsion (Module.finrank k E)) := by
  let n := Module.finrank k E
  letI : NeZero n := ⟨Nat.ne_of_gt (Module.finrank_pos (R := k) (M := E))⟩
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
          have hadd := congrArg Multiplicative.toAdd hx
          simpa using hadd
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
    rw [hcard, invariant_torsion_card n]
  exact MulEquiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).2 ⟨hf, hcards⟩)

/-- Universe-polymorphic local cardinality input needed by the invariant-sum
argument.  The existing theorem `h_card_finrank` proves
this at universe zero; transporting that proof to the resized local
cohomology used here remains a separate formalization task. -/
def CyclicRelativeCardinality : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K)),
    Nat.card
        (localRelativeBrauer K L completion (.inl P)) =
      finiteCompletionDegree (K := K) (L := L)
        ⟨P, hasseChosenPlace completion (.inl P)⟩

set_option synthInstance.maxHeartbeats 300000 in
-- The singleton selection and its completion fields are deeply dependent.
set_option maxHeartbeats 4000000 in
-- Spectral base change unfolds the local relative Brauer equivalence.
/-- The finite local cardinality input is a consequence of the spectral
base-change formula already required by the absolute kernel-lifting side of
VIII.4.2.  A singleton selection exposes an arbitrary chosen completion to
`FiniteSpectralChange`. -/
theorem cardinality_spectral_change
    (hbaseChange : FiniteSpectralChange.{u}) :
    CyclicRelativeCardinality.{u} := by
  classical
  intro K L _ _ _ _ _ _ _ _ completion P
  let S : Finset (finitePrime K) := {P}
  let selected : ∀ Q : S,
      ICohomo.CompletionPlacesAbove
        (L := L) (FinitePlace.mk Q.1).val :=
    fun Q ↦ hasseChosenPlace completion (.inl Q.1)
  let selection : FiniteCompletionSelection K L S 1 :=
    { completion := completion
      selected := selected
      chosen_eq_selected := fun _ ↦ rfl
      degree_dvd := fun _ ↦ one_dvd _ }
  let Q : S := ⟨P, by simp [S]⟩
  let v := (FinitePlace.mk P).val
  let w := hasseChosenPlace completion (.inl P)
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
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
  letI : Finite
      (ICohomo.CompletionPlacesAbove (L := L) v) :=
    absolute_extensions_separable v
  letI : Nonempty
      (ICohomo.CompletionPlacesAbove (L := L) v) :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (ICohomo.CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  have hlocal : SpectralChangeFormula
      v.Completion w.1.Completion := by
    simpa only [S, Q, selection, selected, v, w] using
      hbaseChange K L S 1 selection Q
  change Nat.card (relativeBrauerGroup v.Completion w.1.Completion) =
    Module.finrank v.Completion w.1.Completion
  exact relative_spectral_change
    v.Completion w.1.Completion hlocal

set_option synthInstance.maxHeartbeats 500000 in
-- The chosen completion and its stabilizer are dependent on the finite place.
set_option maxHeartbeats 5000000 in
-- The direct local cardinality proof normalizes both cohomology presentations.
/-- The finite local cardinality input is unconditional on the cyclic route:
the direct local Herbrand calculation computes it without invariant base
change. -/
theorem relative_cardinality_direct :
    CyclicRelativeCardinality.{u} := by
  intro K L _ _ _ _ _ _ _ _ completion P
  let v := (FinitePlace.mk P).val
  let w := hasseChosenPlace completion (.inl P)
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  change Nat.card (relativeBrauerGroup v.Completion w.1.Completion) =
    Module.finrank v.Completion w.1.Completion
  exact relative_brauer_direct P w

set_option synthInstance.maxHeartbeats 300000 in
-- Chosen completion fields require deeper instance synthesis.
set_option maxHeartbeats 4000000 in
-- Local field, completion Galois, and dependent relative-Brauer instances are deep.
/-- The invariant of one finite relative Brauer component realizes every
class killed by that component's local degree, viewed inside the
global-degree torsion subgroup. -/
theorem component_hits_torsion
    [IsCyclic Gal(L/K)]
    (hlocalCard : CyclicRelativeCardinality.{u})
    (completion : HasseCompletionData K L)
    (data : BData K)
    (P : HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hdvd : finiteCompletionDegree (K := K) (L := L)
      ⟨P, hasseChosenPlace completion (.inl P)⟩ ∣
        Module.finrank K L)
    (t : localInvariantTorsion
      (finiteCompletionDegree (K := K) (L := L)
        ⟨P, hasseChosenPlace completion (.inl P)⟩)) :
    ∃ beta : Additive
        (localRelativeBrauer K L completion (.inl P)),
      cyclicRelativeInvariant K L completion
          data.placeInvariant
          (relative_local_torsion K L completion data) (.inl P)
          beta =
        torsionInclusionDvd _ _ hdvd t := by
  let v := (FinitePlace.mk P).val
  let w := hasseChosenPlace completion (.inl P)
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
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
  letI : Finite
      (ICohomo.CompletionPlacesAbove (L := L) v) :=
    absolute_extensions_separable v
  letI : Nonempty
      (ICohomo.CompletionPlacesAbove (L := L) v) :=
    absolute_value_extension (K := K) (L := L) v
  letI : MulAction.IsPretransitive Gal(L/K)
      (ICohomo.CompletionPlacesAbove (L := L) v) :=
    completion_above_pretransitive P
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : FiniteDimensional v.Completion w.1.Completion :=
    Towers.NumberTheory.Milne.placeCompletionDimensional v w
  letI : IsGalois v.Completion w.1.Completion :=
    placeCompletionGalois v w
  have hcard : Nat.card
      (relativeBrauerGroup v.Completion w.1.Completion) =
      Module.finrank v.Completion w.1.Completion :=
    hlocalCard K L completion P
  let e : relativeBrauerGroup v.Completion w.1.Completion ≃*
      Multiplicative
        (localInvariantTorsion
          (Module.finrank v.Completion w.1.Completion)) :=
    relativeBrauerCardinality
      v.Completion w.1.Completion hcard
  let beta : relativeBrauerGroup v.Completion w.1.Completion :=
    e.symm (Multiplicative.ofAdd t)
  refine ⟨Additive.ofMul beta, Subtype.ext ?_⟩
  have heAdd := congrArg Multiplicative.toAdd
    (e.apply_symm_apply (Multiplicative.ofAdd t))
  have heVal := congrArg
    (fun z : localInvariantTorsion
        (Module.finrank v.Completion w.1.Completion) ↦
      (z : LocalInvariant)) heAdd
  simpa only [cyclicRelativeInvariant,
    localBrauerInclusion,
    localRelativeBrauer, hasseAbsoluteValue,
    chosenCompletionExtension,
    data.placeInvariant.finite_eq P, finitePlaceInvariant,
    beta, e, torsionInclusionDvd,
    relativeBrauerCardinality,
    finiteCompletionDegree] using heVal

set_option synthInstance.maxHeartbeats 300000 in
-- Direct-sum component types contain dependent completion fields.
set_option maxHeartbeats 4000000 in
-- The chosen component and direct-sum family are dependent on the place.
/-- A Frobenius family makes the complete finite-cyclic invariant sum
surjective.  Each selected component contributes the subgroup killed by its
local degree.  Since the Frobenius orders generate the cyclic Galois group,
those local degrees force the range to have cardinality divisible by the
global degree; Lagrange's theorem forces the range to be the whole target. -/
theorem relative_frobenius_family
    [IsCyclic Gal(L/K)]
    (hlocalCard : CyclicRelativeCardinality.{u})
    (frobenius : FFam K L)
    (completion : HasseCompletionData K L)
    (data : BData K) :
    Function.Surjective
      (relativeInvariantSum K L completion data.placeInvariant
        (relative_local_torsion K L completion data)) := by
  classical
  let n := Module.finrank K L
  let sum := relativeInvariantSum K L completion
    data.placeInvariant
      (relative_local_torsion K L completion data)
  letI : NeZero n := ⟨Nat.ne_of_gt (Module.finrank_pos (R := K) (M := L))⟩
  letI : Finite (localInvariantTorsion n) :=
    Finite.of_equiv (ZMod n) (torsionZMod n)
  letI : Finite sum.range :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hselected (i : frobenius.index) :
      finiteCompletionDegree (K := K) (L := L)
          ⟨frobenius.prime i, frobenius.upper i⟩ ∣
        Nat.card sum.range := by
    let P := frobenius.prime i
    let chosen := hasseChosenPlace completion (.inl P)
    let d := finiteCompletionDegree (K := K) (L := L) ⟨P, chosen⟩
    have hdegree : d = finiteCompletionDegree (K := K) (L := L)
        ⟨frobenius.prime i, frobenius.upper i⟩ :=
      finite_completion_degree
        (K := K) (L := L) P chosen (frobenius.upper i)
    have hdvd : d ∣ n := by
      exact degree_dvd_global
        (K := K) (L := L) (⟨P, chosen⟩ : FiniteCompletion K L)
    let inclusion := torsionInclusionDvd d n hdvd
    have hinclusion : Function.Injective inclusion :=
      torsion_inclusion_injective d n hdvd
    have hrange : inclusion.range ≤ sum.range := by
      rintro y ⟨t, rfl⟩
      obtain ⟨beta, hbeta⟩ :=
        component_hits_torsion
          K L hlocalCard completion data P hdvd t
      refine ⟨DirectSum.of
        (fun v : NumberFieldPlace K ↦
          Additive (localRelativeBrauer K L completion v))
        (.inl P) beta, ?_⟩
      change (DirectSum.toAddMonoid
        (cyclicRelativeInvariant K L completion
          data.placeInvariant
          (relative_local_torsion K L completion data)))
          (DirectSum.of
            (fun v : NumberFieldPlace K ↦
              Additive (localRelativeBrauer K L completion v))
            (.inl P) beta) = inclusion t
      rw [DirectSum.toAddMonoid_of, hbeta]
    let inclusionToRange : localInvariantTorsion d →+ sum.range :=
      inclusion.codRestrict sum.range fun t ↦
        hrange (Set.mem_range_self t)
    have hdpos : 0 < d :=
      completion_degree_pos
        (K := K) (L := L) (⟨P, chosen⟩ : FiniteCompletion K L)
    letI : NeZero d := ⟨Nat.ne_of_gt hdpos⟩
    rw [← hdegree, ← invariant_torsion_card d]
    exact AddSubgroup.card_dvd_of_injective inclusionToRange fun x y hxy ↦
      hinclusion (congrArg Subtype.val hxy)
  have hn_dvd_range : n ∣ Nat.card sum.range :=
    frobenius.globaldegree_dvdlocal_degreesdvd
      (Nat.card sum.range) hselected
  have hrange_dvd_n : Nat.card sum.range ∣ n := by
    rw [← invariant_torsion_card n]
    exact AddSubgroup.card_addSubgroup_dvd_card sum.range
  have hrange_card : Nat.card sum.range =
      Nat.card (localInvariantTorsion n) := by
    rw [invariant_torsion_card n]
    exact (Nat.dvd_antisymm hn_dvd_range hrange_dvd_n).symm
  apply AddMonoidHom.range_eq_top.mp
  exact AddSubgroup.eq_top_of_card_eq sum.range hrange_card

set_option maxHeartbeats 4000000 in
-- The comparison theorem unfolds both dependent local direct sums.
/-- VII.8.1 gives reciprocity for the concrete cohomological relative
localization once it is compared with the localization in the same
`BData`. -/
theorem cyclic_relative_reciprocity
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      LFTheory.AbsoluteAbelianGalois K)
    (hphi : ContinuousGlobalArtin phi)
    (completion : HasseCompletionData K L)
    (data : BData K)
    (beta : Additive (relativeBrauerGroup K L)) :
    data.placeInvariant.sum K
      (brauerDirectInclusion K L completion
        (brauerCohomologicalLocalization K L completion beta)) = 0 := by
  have hreciprocity := (h81 K phi data hphi).2 L beta.toMul
  change data.placeInvariant.sum K
      (data.localization.localization
        (Additive.ofMul (beta.toMul : BrauerGroup K))) = 0 at hreciprocity
  rw [localization_brauer_cohomological
    K L completion data beta] at hreciprocity
  exact hreciprocity

set_option synthInstance.maxHeartbeats 300000 in
-- The invariant sum is defined on the chosen-completion dependent family.
/-- The actual arithmetic bottom-row input.  Local invariant theory and
VIII.4.1 must construct the surjective map; VII.8.1 supplies `reciprocity`.
All factorization through the obstruction image is derived below. -/
structure CyclicRelativeData
    [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K) where
  invariantSum : CyclicRelativeSum K L completion →+
    localInvariantTorsion (Module.finrank K L)
  invariantSum_coe : ∀ y,
    ((invariantSum y : localInvariantTorsion (Module.finrank K L)) :
        LocalInvariant) =
      placeInvariant.sum K
        (brauerDirectInclusion K L completion y)
  reciprocity : ∀ beta,
    invariantSum
      (brauerCohomologicalLocalization K L completion beta) = 0
  surjective : Function.Surjective invariantSum

set_option synthInstance.maxHeartbeats 300000 in
-- Later fields depend on the pointwise torsion proof for the constructed sum.
/-- The three arithmetic facts still required to construct the bottom row:
local invariant torsion, global reciprocity, and surjectivity. -/
structure InvariantArithmeticData
    [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K) where
  local_torsion : ∀ (v : NumberFieldPlace K)
    (beta : Additive (localRelativeBrauer K L completion v)),
    Module.finrank K L •
      placeInvariant.invariant v
        (localBrauerInclusion K L completion v beta) = 0
  reciprocity : ∀ beta,
    placeInvariant.sum K
      (brauerDirectInclusion K L completion
        (brauerCohomologicalLocalization K L completion beta)) = 0
  surjective : Function.Surjective
    (relativeInvariantSum
      K L completion placeInvariant local_torsion)

set_option synthInstance.maxHeartbeats 300000 in
-- The surjectivity field depends on the pointwise torsion proof.
/-- Data-aware finite-cyclic input after VII.8.1 has discharged reciprocity.
Only local invariant torsion and surjectivity remain. -/
structure RelativeInvariantData
    [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (data : BData K) where
  local_torsion : ∀ (v : NumberFieldPlace K)
    (beta : Additive (localRelativeBrauer K L completion v)),
    Module.finrank K L •
      data.placeInvariant.invariant v
        (localBrauerInclusion K L completion v beta) = 0
  surjective : Function.Surjective
    (relativeInvariantSum
      K L completion data.placeInvariant local_torsion)

/-- After unconditional pointwise torsion, surjectivity is the only local
finite-cyclic arithmetic datum still needed. -/
structure InvariantSurjectivityData
    [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (data : BData K) where
  surjective : Function.Surjective
    (relativeInvariantSum K L completion data.placeInvariant
      (relative_local_torsion K L completion data))

/-- Surjectivity data supplies the older two-field local-invariant data;
pointwise torsion is filled by Corollary IV.3.17 and local-degree
divisibility. -/
noncomputable def cyclic_relative_surjectivity
    [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (data : BData K)
    (hsurj : InvariantSurjectivityData
      K L completion data) :
    RelativeInvariantData K L completion data where
  local_torsion := relative_local_torsion K L completion data
  surjective := hsurj.surjective

/-- VII.8.1 adds reciprocity to the two local-invariant inputs above. -/
noncomputable def relative_invariant_arithmetic
    [IsCyclic Gal(L/K)]
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      LFTheory.AbsoluteAbelianGalois K)
    (hphi : ContinuousGlobalArtin phi)
    (completion : HasseCompletionData K L)
    (data : BData K)
    (localData : RelativeInvariantData K L completion data) :
    InvariantArithmeticData
      K L completion data.placeInvariant where
  local_torsion := localData.local_torsion
  reciprocity := cyclic_relative_reciprocity
    K L h81 phi hphi completion data
  surjective := localData.surjective

set_option maxHeartbeats 4000000 in
-- The reciprocity proof compares dependent direct sums through the coe theorem.
/-- The three arithmetic facts above construct the minimal invariant-sum
data used by the formal cardinality argument. -/
noncomputable def cyclic_relative_arithmetic
    [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K)
    (data : InvariantArithmeticData
      K L completion placeInvariant) :
    CyclicRelativeData K L completion placeInvariant where
  invariantSum := relativeInvariantSum
    K L completion placeInvariant data.local_torsion
  invariantSum_coe := relative_invariant_coe
    K L completion placeInvariant data.local_torsion
  reciprocity beta := by
    apply Subtype.ext
    exact (relative_invariant_coe
      K L completion placeInvariant data.local_torsion
      (brauerCohomologicalLocalization K L completion beta)).trans
        (data.reciprocity beta)
  surjective := data.surjective

set_option synthInstance.maxHeartbeats 300000 in
-- Every field mentions the chosen-completion dependent direct sum.
/-- The remaining bottom-row data after the top cohomological row and its
cardinality bound have been constructed.  This is the precise formal target
for VII.8.1, the local invariant image calculation, and VIII.4.1. -/
structure InvariantFactorizationData
    [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K) where
  invariantSum : CyclicRelativeSum K L completion →+
    localInvariantTorsion (Module.finrank K L)
  invariantSum_coe : ∀ y,
    ((invariantSum y : localInvariantTorsion (Module.finrank K L)) :
        LocalInvariant) =
      placeInvariant.sum K
        (brauerDirectInclusion K L completion y)
  inducedInvariant :
    (relativeLocalObstruction K L completion).range →+
      localInvariantTorsion (Module.finrank K L)
  inducedInvariant_factor : ∀ y,
    invariantSum y = inducedInvariant
      ⟨relativeLocalObstruction K L completion y,
        Set.mem_range_self y⟩
  inducedInvariant_surjective : Function.Surjective inducedInvariant

set_option maxHeartbeats 4000000 in
-- Exactness unfolds the dependent local direct sum and the obstruction map.
/-- The actual invariant sum, reciprocity, and surjectivity automa
produce the factorization data used in the cardinality squeeze. -/
noncomputable def relative_invariant_factorization
    [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K)
    (data : CyclicRelativeData
      K L completion placeInvariant) :
    InvariantFactorizationData
      K L completion placeInvariant := by
  let g := relativeLocalObstruction K L completion
  let f := brauerCohomologicalLocalization K L completion
  have hker : g.ker ≤ data.invariantSum.ker :=
    ker_exact_comp f g data.invariantSum
      (top_row_exact K L completion) data.reciprocity
  exact
    { invariantSum := data.invariantSum
      invariantSum_coe := data.invariantSum_coe
      inducedInvariant :=
        monoidDescendRange g data.invariantSum hker
      inducedInvariant_factor := fun y ↦ by
        exact (monoid_descend_range
          g data.invariantSum hker y).symm
      inducedInvariant_surjective :=
        monoid_descend_surjective
          g data.invariantSum hker data.surjective }

/-- The remaining arithmetic bridge in its smallest checked form: construct
the relative invariant sum, prove global reciprocity, and prove that the sum
is onto the `[L:K]`-torsion subgroup. -/
def CyclicRelativeBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K),
    Nonempty (CyclicRelativeData
      K L completion placeInvariant)

/-- The final finite-cyclic arithmetic boundary, with every formal
factorization and direct-sum construction removed. -/
def InvariantArithmeticBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K),
    Nonempty (InvariantArithmeticData
      K L completion placeInvariant)

/-- The exact remaining finite-cyclic bridge for the data-aware VIII.4.2
assembly. Recip is intentionally absent because VII.8.1 supplies it. -/
def RelativeInvariantBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (data : BData K),
    Nonempty (RelativeInvariantData K L completion data)

/-- The exact remaining finite-cyclic arithmetic bridge: the canonical
relative invariant sum is onto the `[L:K]`-torsion subgroup. -/
def InvariantSurjectivityBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (data : BData K),
    Nonempty (InvariantSurjectivityData
      K L completion data)

/-- Surjectivity alone implies the data-aware local-invariant bridge. -/
theorem invariant_bridge_surjectivity
    (hsurj : InvariantSurjectivityBridge.{u}) :
    RelativeInvariantBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _ completion data
  obtain ⟨h⟩ := hsurj K L completion data
  exact ⟨cyclic_relative_surjectivity
    K L completion data h⟩

/-- Lemma VIII.4.1's Frobenius-family input proves the remaining invariant
surjectivity bridge. -/
theorem surjectivity_bridge_frobenius
    (hlocalCard : CyclicRelativeCardinality.{u})
    (h41 : ArtinFrobeniusBridge.{u}) :
    InvariantSurjectivityBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _ completion data
  obtain ⟨frobenius⟩ := h41 K L
  exact ⟨{
    surjective :=
      relative_frobenius_family
        K L hlocalCard frobenius completion data }⟩

/-- Proposition VII.4.7 now supplies all Frobenius input needed for relative
invariant-sum surjectivity; ramification finiteness and the local
degree/order comparison are proved in the VIII.4.1 module. -/
theorem invariantSurjectivityBridge
    (hlocalCard : CyclicRelativeCardinality.{u})
    (h47 : FrobeniusGeneration.{u}) :
    InvariantSurjectivityBridge.{u} :=
  surjectivity_bridge_frobenius
    hlocalCard (artin_bridge_data h47)

/-- On the final VIII.4.2 route, finite spectral base change supplies the
local cardinality input, so Proposition VII.4.7 is the only additional
surjectivity assumption. -/
theorem surjectivity_change_frobenius
    (hbaseChange : FiniteSpectralChange.{u})
    (h47 : FrobeniusGeneration.{u}) :
    InvariantSurjectivityBridge.{u} :=
  invariantSurjectivityBridge
    (cardinality_spectral_change
      hbaseChange)
    h47

/-- The fixed-field proof of Proposition VII.4.7 reduces the final
surjectivity input further to Proposition VII.4.6. -/
theorem surjectivity_nonsplit_primes
    (hbaseChange : FiniteSpectralChange.{u})
    (h46 : Towers.CField.NIndex.NontrivialNonsplitPrimes.{u}) :
    InvariantSurjectivityBridge.{u} :=
  surjectivity_change_frobenius
    hbaseChange
    (Towers.CField.NIndex.numberElementStatement
      h46)

/-- The dense-subgroup degree-one conclusion supplied by Lemma VII.4.5. -/
private abbrev SolvableDenseDegreeBridge : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [IsSolvable Gal(L/K)],
    ∀ D : Subgroup (IdeleGroup (NumberField.RingOfIntegers K) K),
      D ≤ ideleNormSubgroup (K := K) (L := L) →
      Dense ((principalIdeles (NumberField.RingOfIntegers K) K ⊔ D :
        Subgroup (IdeleGroup (NumberField.RingOfIntegers K) K)) :
          Set (IdeleGroup (NumberField.RingOfIntegers K) K)) →
      Module.finrank K L = 1

/-- With weak approximation discharged, the arithmetic surjectivity bridge
uses Lemma VII.4.5 and split-away idèle-norm assembly directly. -/
theorem surjectivity_change_away
    (hbaseChange : FiniteSpectralChange.{u})
    (h45 : SolvableDenseDegreeBridge.{u})
    (hnorm : Towers.CField.NIndex.SplitAwayBridge.{u}) :
    InvariantSurjectivityBridge.{u} :=
  surjectivity_change_frobenius
    hbaseChange
    (NIndex.statement_split_away
      h45 hnorm)

/-- The finite-cyclic surjectivity bridge now depends only on the spectral
base-change input and Lemma VII.4.5. -/
theorem surjectivity_change_subextension
    (hbaseChange : FiniteSpectralChange.{u})
    (h45 : SolvableDenseDegreeBridge.{u}) :
    InvariantSurjectivityBridge.{u} :=
  surjectivity_change_frobenius
    hbaseChange
    (NIndex.number_statement_only h45)

/-- The local invariant sum is unconditionally surjective on the finite
cyclic route.  Direct local Herbrand cardinality supplies the component
sizes, while the already-proved Lemma VII.4.5 supplies Frobenius generation. -/
theorem surjectivity_bridge_direct :
    InvariantSurjectivityBridge.{u} :=
  surjectivity_bridge_frobenius
    relative_cardinality_direct
    (artin_away_only cyclicSubextensionDegree)

/-- The three arithmetic assertions imply the minimal invariant-sum bridge. -/
theorem relative_bridge_arithmetic
    (harithmetic : InvariantArithmeticBridge.{u}) :
    CyclicRelativeBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _ completion placeInvariant
  obtain ⟨data⟩ := harithmetic K L completion placeInvariant
  exact ⟨cyclic_relative_arithmetic
    K L completion placeInvariant data⟩

set_option maxHeartbeats 4000000 in
-- Installing finiteness and elaborating the dependent direct sum is costly.
/-- VII.5.1 and the remaining invariant-factorization data construct all
fields of `RelativeSequenceData`. -/
noncomputable def relativeSequenceData
    [IsCyclic Gal(L/K)]
    (h51 : IdeleCohomologyClaims.{u})
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K)
    (data : InvariantFactorizationData
      K L completion placeInvariant) :
    RelativeSequenceData K L completion placeInvariant := by
  letI : Finite (finiteRelativeObstruction K L) :=
    cyclic_relative_obstruction K L h51
  letI : Fintype (finiteRelativeObstruction K L) :=
    Fintype.ofFinite (finiteRelativeObstruction K L)
  exact
    { Obstruction := finiteRelativeObstruction K L
      localToObstruction :=
        relativeLocalObstruction K L completion
      top_exact := top_row_exact K L completion
      invariantSum := data.invariantSum
      invariantSum_coe := data.invariantSum_coe
      inducedInvariant := data.inducedInvariant
      inducedInvariant_factor := data.inducedInvariant_factor
      inducedInvariant_surjective := data.inducedInvariant_surjective
      obstruction_card_le := by
        simpa only [Nat.card_eq_fintype_card] using
          relative_obstruction_card K L h51 }

/-- The exact remaining finite-cyclic bridge after discharging the complete
top row and its VII.5.1 cardinality estimate. -/
def InvariantFactorizationBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K),
    Nonempty (InvariantFactorizationData
      K L completion placeInvariant)

/-- The invariant-sum bridge automa supplies the older explicit
factorization bridge. -/
theorem factorization_bridge_sum
    (hsum : CyclicRelativeBridge.{u}) :
    InvariantFactorizationBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _ completion placeInvariant
  obtain ⟨data⟩ := hsum K L completion placeInvariant
  exact ⟨relative_invariant_factorization
    K L completion placeInvariant data⟩

/-- The old whole-sequence bridge follows from VII.5.1 and only the
remaining bottom-row factorization bridge. -/
theorem sequenceCohomologyBridge
    (h51 : IdeleCohomologyClaims.{u})
    (hinvariant : InvariantFactorizationBridge.{u}) :
    SequenceCohomologyBridge.{u} := by
  intro K L _ _ _ _ _ _ _ _ completion placeInvariant
  obtain ⟨data⟩ := hinvariant K L completion placeInvariant
  exact ⟨relativeSequenceData
    K L h51 completion placeInvariant data⟩

/-- VII.5.1 and the minimal invariant-sum bridge imply the whole
finite-cyclic cohomological bridge. -/
theorem sequence_cohomology_bridge
    (h51 : IdeleCohomologyClaims.{u})
    (hsum : CyclicRelativeBridge.{u}) :
    SequenceCohomologyBridge.{u} :=
  sequenceCohomologyBridge h51
    (factorization_bridge_sum hsum)

set_option maxHeartbeats 4000000 in
-- This composes all dependent finite-cyclic data constructors.
/-- For one `BData`, VII.5.1, VII.8.1, local torsion, and
surjectivity construct the complete sequence data. -/
noncomputable def relative_sequence_invariant
    [IsCyclic Gal(L/K)]
    (h51 : IdeleCohomologyClaims.{u})
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (phi : IdeleGroup (NumberField.RingOfIntegers K) K →*
      LFTheory.AbsoluteAbelianGalois K)
    (hphi : ContinuousGlobalArtin phi)
    (completion : HasseCompletionData K L)
    (data : BData K)
    (localData : RelativeInvariantData K L completion data) :
    RelativeSequenceData
      K L completion data.placeInvariant :=
  relativeSequenceData K L h51 completion
    data.placeInvariant
      (relative_invariant_factorization
        K L completion data.placeInvariant
          (cyclic_relative_arithmetic
            K L completion data.placeInvariant
              (relative_invariant_arithmetic
                K L h81 phi hphi completion data localData)))

set_option maxHeartbeats 4000000 in
-- The sequence data carries a deeply dependent chosen-completion family.
/-- The data-aware finite cyclic kernel theorem follows from only local
torsion and invariant-sum surjectivity; reciprocity is supplied by VII.8.1. -/
theorem brauer_lifting_bridge
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (hlocal : RelativeInvariantBridge.{u}) :
    BrauerLiftingData.{u} := by
  intro K L _ _ _ _ _ _ _ _ completion data y hy
  obtain ⟨phi, hphi, _⟩ := hArtin K
  obtain ⟨localData⟩ := hlocal K L completion data
  let sequence := relative_sequence_invariant
    K L h51 h81 phi hphi completion data localData
  have hexact := relative_exact_data
    K L completion data.placeInvariant sequence
  apply (hexact y).mp
  apply Subtype.ext
  exact (sequence.invariantSum_coe y).trans hy

/-- The most expanded current source-statement route: the finite cyclic
relative input has been reduced past its entire cohomological top row to the
local invariant factorization and surjectivity assertions. -/
theorem cohomology_factorization_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (hinvariant : InvariantFactorizationBridge.{u}) :
    GlobalLocalizationSequence.{u} :=
  cohomological_arithmetic_components
    h51 hArtin h81 h73 hbaseChange
      (sequenceCohomologyBridge
        h51 hinvariant)

/-- Final VIII.4.2 route with the finite-cyclic input reduced to the actual
local invariant sum, its reciprocity law, and its surjectivity. -/
theorem cohomology_invariant_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (hsum : CyclicRelativeBridge.{u}) :
    GlobalLocalizationSequence.{u} :=
  cohomological_arithmetic_components
    h51 hArtin h81 h73 hbaseChange
      (sequence_cohomology_bridge
        h51 hsum)

/-- Most expanded checked endpoint: only local invariant torsion,
reciprocity, and surjectivity remain on the finite-cyclic side. -/
theorem cohomology_arithmetic_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (hfiniteCyclic : InvariantArithmeticBridge.{u}) :
    GlobalLocalizationSequence.{u} :=
  cohomology_invariant_components
    h51 hArtin h81 h73 hbaseChange
      (relative_bridge_arithmetic
        hfiniteCyclic)

/-- Most expanded data-aware endpoint: VII.8.1 now supplies finite-cyclic
reciprocity, leaving only pointwise local torsion and sum surjectivity. -/
theorem relative_cohomology_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (hlocal : RelativeInvariantBridge.{u}) :
    GlobalLocalizationSequence.{u} :=
  exactness_assembly_lifting
    h51 hArtin h81
      (lifting_killing_data
        (killing_construction_change
          h73 hbaseChange)
        (brauer_lifting_bridge
          h51 hArtin h81 hlocal))

/-- Most expanded checked endpoint: the finite-cyclic side now requires only
surjectivity of its canonical invariant sum. -/
theorem cohomology_surjectivity_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (hsurj : InvariantSurjectivityBridge.{u}) :
    GlobalLocalizationSequence.{u} :=
  relative_cohomology_components
    h51 hArtin h81 h73 hbaseChange
      (invariant_bridge_surjectivity hsurj)

/-- Fully expanded checked route through the printed proof.  The
finite-cyclic relative sequence is now derived from Lemma VIII.4.1's exact
Artin/Frobenius input rather than retained as a separate bridge. -/
theorem fully_expanded_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (hlocalCard : CyclicRelativeCardinality.{u})
    (h41 : ArtinFrobeniusBridge.{u}) :
    GlobalLocalizationSequence.{u} :=
  cohomology_surjectivity_components
    h51 hArtin h81 h73 hbaseChange
      (surjectivity_bridge_frobenius
        hlocalCard h41)

/-- Fully expanded route with Lemma VIII.4.1 and finite local cardinality
discharged: the finite-cyclic side depends directly on Proposition VII.4.7
and the finite base-change formula already used by kernel lifting. -/
theorem cohomology_frobenius_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (h47 : FrobeniusGeneration.{u}) :
    GlobalLocalizationSequence.{u} :=
  cohomology_surjectivity_components
    h51 hArtin h81 h73 hbaseChange
      (surjectivity_change_frobenius
        hbaseChange h47)

/-- Fully expanded route with the fixed-field Frobenius-generation argument
discharged: the sixth upstream input is Proposition VII.4.6. -/
theorem localization_nonsplit_primes
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (h46 : Towers.CField.NIndex.NontrivialNonsplitPrimes.{u}) :
    GlobalLocalizationSequence.{u} :=
  cohomology_surjectivity_components
    h51 hArtin h81 h73 hbaseChange
      (surjectivity_nonsplit_primes
        hbaseChange h46)

/-- Fully expanded VIII.4.2 route after formalizing the weak-approximation
half of Proposition VII.4.6. -/
theorem split_away_norm_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (h45 : SolvableDenseDegreeBridge.{u})
    (hnorm : Towers.CField.NIndex.SplitAwayBridge.{u}) :
    GlobalLocalizationSequence.{u} :=
  cohomology_surjectivity_components
    h51 hArtin h81 h73 hbaseChange
      (surjectivity_change_away
        hbaseChange h45 hnorm)

/-- Fully expanded VIII.4.2 route after internalizing both halves of
Proposition VII.4.6; its remaining VII.4 input is Lemma VII.4.5. -/
theorem split_away_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (h45 : SolvableDenseDegreeBridge.{u}) :
    GlobalLocalizationSequence.{u} :=
  cohomology_surjectivity_components
    h51 hArtin h81 h73 hbaseChange
      (surjectivity_change_subextension
        hbaseChange h45)

/-- Fully expanded VIII.4.2 route after proving the cyclic-subextension,
idèle-norm transitivity, and norm-range openness inputs to Lemma VII.4.5. -/
theorem spectral_change_components
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u})
    (hbaseChange : FiniteSpectralChange.{u})
    (hfirst : FirstInequality.{u}) :
    GlobalLocalizationSequence.{u} :=
  split_away_components
    h51 hArtin h81 h73 hbaseChange
      (localization_cokernel_assembly hfirst)

/-- Sharp current endpoint for VIII.4.2.  The direct local Herbrand
calculation discharges both former uses of finite spectral base change, and
the Chapter VII.4 assembly discharges the finite-cyclic surjectivity input. -/
theorem direct_cardinality_construction
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L)))
    (h73 : FinitePrime.{u}) :
    GlobalLocalizationSequence.{u} :=
  exactness_assembly_lifting
    h51 hArtin h81
      (lifting_killing_data
        (killing_cyclotomic_construction h73)
        (brauer_lifting_bridge
          h51 hArtin h81
          (invariant_bridge_surjectivity
            surjectivity_bridge_direct)))

/-- Sharp VIII.4.2 endpoint after discharging Lemma VII.7.3.  Only
VII.5.1, the global Artin map, and VII.8.1 remain as inputs. -/
theorem cohomology_direct_cardinality
    (h51 : IdeleCohomologyClaims.{u})
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L))) :
    GlobalLocalizationSequence.{u} :=
  direct_cardinality_construction
    h51 hArtin h81 rationalBaseChange

/-- Theorem VII.5.1 is now supplied by the algebraic second-inequality
proof in §VII.6.  At this endpoint, VIII.4.2 has only the global Artin map
and Theorem VII.8.1 as upstream inputs. -/
theorem global_artin_fundamental
    (hArtin : ∀ (K : Type u) [Field K] [NumberField K],
      GlobalArtinProposition (K := K))
    (h81 : (∀ (K : Type u) [Field K] [NumberField K]
        (phi : IdeleGroup (NumberField.RingOfIntegers K) K →* AbsoluteAbelianGalois K)
        (data : BData K), ContinuousGlobalArtin phi →
        (∀ E : FASubext K,
          TrivialPrincipalIdeles (NumberField.RingOfIntegers K) K Gal(E.1/K)
            ((localAbelianRestriction E).comp phi)) ∧
        (∀ (L : Type u) [Field L] [NumberField L] [Algebra K L]
          [FiniteDimensional K L] [IsGalois K L],
            InvariantSumReciprocity K data L))) :
    GlobalLocalizationSequence.{u} :=
  cohomology_direct_cardinality
    Towers.CField.CIdeles.ideleCohomologyClaims
    hArtin h81

end

end Towers.CField.BLoc

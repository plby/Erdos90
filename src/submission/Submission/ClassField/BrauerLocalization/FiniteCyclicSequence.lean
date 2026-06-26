import Submission.ClassField.BrauerLocalization.KillingSelection
import Submission.ClassField.GlobalClass.CardinalityRigidity

/-!
# Finite cyclic relative Brauer sequence for VIII.4.2

The last finite-group step in the printed proof of Theorem VIII.4.2 is a
cardinality squeeze.  A local-to-global obstruction map is exact after
relative Brauer localization; its image maps surjectively to the cyclic
group of local invariants; and the obstruction group has cardinality at
most the order of that cyclic group.  Hence the induced map on the image is
injective, and the relative Brauer localization is exact against the local
invariant sum.

This file first proves that finite-group argument abstractly.  It then
packages the still-arithmetic inputs in the concrete relative-Brauer setting
and derives the kernel-lifting statement consumed by `KernelLiftingAssembly`.
-/

namespace Submission.CField.BLoc

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne
open Submission.CField.BGroups
open Submission.CField.LFTheory
open Submission.CField.LBrauer
open Submission.CField.Ideles
open Submission.CField.Recip
open Submission.CField.CIdeles
open Submission.CField.CBrauer
open Submission.CField.RExist
open Submission.CField.HNorm
open Submission.CField.GClass

noncomputable section

universe u

/-- The finite-cardinality squeeze behind the bottom-row exactness in the
proof of VIII.4.2.  The map `q` is the map induced from `s` on the range of
the obstruction map `g`. -/
theorem exact_factorization_card
    {A B C T : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup T]
    [Fintype C] [Fintype T]
    (f : A →+ B) (g : B →+ C) (s : B →+ T)
    (hfg : Function.Exact f g)
    (q : g.range →+ T)
    (hfactor : ∀ b, s b = q ⟨g b, Set.mem_range_self b⟩)
    (hq : Function.Surjective q)
    (hcard : Fintype.card C ≤ Fintype.card T) :
    Function.Exact f s := by
  letI : Fintype g.range := Fintype.ofFinite g.range
  have hrangeCard : Fintype.card g.range ≤ Fintype.card T :=
    (Fintype.card_subtype_le (fun c : C ↦ c ∈ g.range)).trans hcard
  have hqInjective : Function.Injective q :=
    injective_surjective_card q hq hrangeCard
  intro b
  constructor
  · intro hsb
    apply (hfg b).mp
    have hqzero : q ⟨g b, Set.mem_range_self b⟩ = q 0 := by
      rw [← hfactor b, hsb, map_zero]
    have hrangeZero := hqInjective hqzero
    exact congrArg Subtype.val hrangeZero
  · intro hb
    have hgb : g b = 0 := (hfg b).mpr hb
    rw [hfactor]
    have hrangeZero : (⟨g b, Set.mem_range_self b⟩ : g.range) = 0 :=
      Subtype.ext hgb
    rw [hrangeZero, map_zero]

set_option synthInstance.maxHeartbeats 300000 in
-- The dependent family unfolds the chosen completion algebra at each place.
/-- The local middle term in the finite cyclic relative Brauer sequence. -/
abbrev CyclicRelativeSum
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (completion : HasseCompletionData K L) :=
  DirectSum (NumberFieldPlace K)
    (fun v ↦ Additive (localRelativeBrauer K L completion v))

set_option synthInstance.maxHeartbeats 300000 in
-- Several fields mention the dependent local relative-Brauer direct sum.
/-- The precise arithmetic and cohomological inputs used by the printed
finite cyclic argument.  `Obstruction` is Milne's `H²(L/K)`, while the range
of `localToObstruction` is his subgroup `H²(L/K)'`.

The last two fields encode the inequality `|H²(L/K)| ≤ [L:K]` and the
fact that the cyclic local invariant target has order `[L:K]`.  The latter
order is supplied below by the canonical equivalence with `ZMod [L:K]`. -/
structure RelativeSequenceData
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K) where
  Obstruction : Type u
  [obstructionAddGroup : AddCommGroup Obstruction]
  [obstructionFintype : Fintype Obstruction]
  localToObstruction :
    CyclicRelativeSum K L completion →+ Obstruction
  top_exact : Function.Exact
    (brauerCohomologicalLocalization K L completion)
    localToObstruction
  invariantSum : CyclicRelativeSum K L completion →+
    localInvariantTorsion (Module.finrank K L)
  invariantSum_coe : ∀ y,
    ((invariantSum y : localInvariantTorsion (Module.finrank K L)) :
        LocalInvariant) =
      placeInvariant.sum K
        (brauerDirectInclusion K L completion y)
  inducedInvariant : localToObstruction.range →+
    localInvariantTorsion (Module.finrank K L)
  inducedInvariant_factor : ∀ y,
    invariantSum y = inducedInvariant
      ⟨localToObstruction y, Set.mem_range_self y⟩
  inducedInvariant_surjective : Function.Surjective inducedInvariant
  obstruction_card_le :
    Fintype.card Obstruction ≤ Module.finrank K L

/-- The remaining finite-cyclic arithmetic bridge, stated in the same
chosen completion models as the relative Brauer localization. -/
def SequenceCohomologyBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K),
    Nonempty (RelativeSequenceData K L completion placeInvariant)

set_option maxHeartbeats 4000000 in
-- The chosen-completion family and its direct sum require deep elaboration.
/-- Concrete finite cyclic sequence data implies exactness of the relative
Brauer localization against its invariant sum. -/
theorem relative_exact_data
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K)
    (data : RelativeSequenceData K L completion placeInvariant) :
    Function.Exact
      (brauerCohomologicalLocalization K L completion)
      data.invariantSum := by
  letI : AddCommGroup data.Obstruction := data.obstructionAddGroup
  letI : Fintype data.Obstruction := data.obstructionFintype
  let n := Module.finrank K L
  letI : NeZero n :=
    ⟨(Module.finrank_pos (R := K) (M := L)).ne'⟩
  letI : Fintype (localInvariantTorsion n) :=
    Fintype.ofEquiv (ZMod n)
      (torsionZMod n).toEquiv
  have htargetCard : Fintype.card (localInvariantTorsion n) = n := by
    calc
      Fintype.card (localInvariantTorsion n) = Fintype.card (ZMod n) :=
        Fintype.card_congr
          (torsionZMod n).symm.toEquiv
      _ = n := ZMod.card n
  apply exact_factorization_card
    (brauerCohomologicalLocalization K L completion)
    data.localToObstruction data.invariantSum data.top_exact
    data.inducedInvariant data.inducedInvariant_factor
    data.inducedInvariant_surjective
  simpa [n, htargetCard] using data.obstruction_card_le

set_option maxHeartbeats 4000000 in
-- Choosing the bridge data elaborates the same dependent direct sum.
/-- The global cohomological bridge implies exactness of each concrete
finite cyclic relative Brauer sequence. -/
theorem exact_cohomology_bridge
    (hbridge : SequenceCohomologyBridge.{u})
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (completion : HasseCompletionData K L)
    (placeInvariant : PIData K) :
    Function.Exact
      (brauerCohomologicalLocalization K L completion)
      ((hbridge K L completion placeInvariant).some.invariantSum) :=
  relative_exact_data K L completion placeInvariant
    (hbridge K L completion placeInvariant).some

set_option maxHeartbeats 4000000 in
-- This specializes exactness to the literal absolute local invariant sum.
/-- The printed finite cyclic cardinality argument supplies the relative
kernel-lifting input needed by the VIII.4.2 assembly. -/
theorem lifting_cohomology_bridge
    (hbridge : SequenceCohomologyBridge.{u}) :
    RelativeBrauerLifting.{u} := by
  intro K L _ _ _ _ _ _ _ _ completion placeInvariant y hy
  let data := (hbridge K L completion placeInvariant).some
  have hexact := relative_exact_data
    K L completion placeInvariant data
  apply (hexact y).mp
  apply Subtype.ext
  exact data.invariantSum_coe y |>.trans hy

/-- The most expanded checked route to VIII.4.2 currently available: the
killing-extension side is reduced to VII.7.3 plus finite local invariant
base change, and the finite cyclic relative side is reduced to the explicit
cohomological sequence data above. -/
theorem cohomological_arithmetic_components
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
    (hrelative : SequenceCohomologyBridge.{u}) :
    GlobalLocalizationSequence.{u} :=
  killing_selection_arithmetic
    h51 hArtin h81 h73 hbaseChange
      (lifting_cohomology_bridge hrelative)

end

end Submission.CField.BLoc

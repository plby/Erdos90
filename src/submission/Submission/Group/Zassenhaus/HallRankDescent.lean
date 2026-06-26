import Submission.Group.HallBasic.AssociatedGradedSpanning
import Submission.Group.Zassenhaus.SignedReductionFactors
import Submission.Group.Zassenhaus.Polynomial
import Submission.Group.Zassenhaus.PolynomialBracketSupport
import Submission.Group.Zassenhaus.SignedCorrectionSemantics
import Mathlib.Data.Prod.Lex
import Submission.Group.HallBasic.OuterValueScaling

/-!
# Hall-rank descent for concrete polynomial inner packets

The classical Hall collector repairs a non-admissible left-normed bracket by
first reducing its inner bracket to atomic Hall-basic trees.  Each resulting
outer bracket then has a strictly smaller reverse finite-rank defect.

Concrete signed-polynomial basic reduction already produces the required
atomic packet.  This file records the bridge from packet membership to indexed
Hall-basic trees and transfers the classical rank-defect decrease to those
symbolic factors.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex
namespace CEWord

universe u

/-- A concrete basic-reduction factor expands to its indexed Hall-basic tree. -/
@[simp]
theorem tree_reduction_factor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree factor.word).weight) :
    tree (basicReductionFactor factor i).word =
      HallTree.indexedBasicTree i :=
  rfl

/--
Every member of a concrete basic-reduction packet expands to an indexed
Hall-basic tree.
-/
theorem indexed_tree_factors
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ basicReductionFactors factor) :
    ∃ i :
        HallTree.BasicIndex
          (α := FreeGenerator.{u} d) (tree factor.word).weight,
      x = basicReductionFactor factor i ∧
        tree x.word = HallTree.indexedBasicTree i := by
  rw [basicReductionFactors] at hx
  rcases List.mem_map.mp hx with ⟨i, _hi, rfl⟩
  exact ⟨i, rfl, tree_reduction_factor factor i⟩

/-- Every tree in a concrete basic-reduction packet is Hall basic. -/
theorem tree_basic_factors
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ basicReductionFactors factor) :
    (tree x.word).IsBasic := by
  rcases indexed_tree_factors factor hx with
    ⟨i, _hx, htree⟩
  rw [htree]
  exact HallTree.indexed_tree i

/-- Every tree in a concrete basic-reduction packet has the inner tree's weight. -/
theorem tree_reduction_factors
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ basicReductionFactors factor) :
    (tree x.word).weight = (tree factor.word).weight := by
  simpa only [tree_weight] using
    word_reduction_factors factor hx

/--
After symbolic inner reduction, bracketing any emitted atom with an unchanged
basic outer tree strictly decreases the classical Hall bracket rank defect.
-/
theorem bracket_defect_factors
    {d : ℕ}
    {ι : Type}
    (inner :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ basicReductionFactors inner)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    HallTree.bracketRankDefect
        ((tree inner.word).weight + unchanged.weight)
        (tree x.word) unchanged <
      HallTree.bracketRankDefect
        ((tree inner.word).weight + unchanged.weight)
        originalLeft originalRight := by
  apply HallTree.bracket_defect_both hRightLeft
  · apply HallTree.weight_add_left added originalRight (tree x.word)
    rw [tree_reduction_factors inner hx, hinnerTree]
    rfl
  · exact hRightUnchanged
  · exact tree_basic_factors inner hx
  · exact hunchangedBasic
  · have hunchangedPos := unchanged.weight_pos
    rw [tree_reduction_factors inner hx]
    omega
  · have hinnerPos := (tree inner.word).weight_pos
    omega

end CEWord
end TCTex
end Submission

/-!
# Bracketing concrete polynomial inner-reduction packets with an outer factor

Explicit Hall reduction replaces an arbitrary concrete signed-polynomial
factor by a finite atomic packet.  To mirror the classical Hall-basis descent,
the next symbolic operation brackets that inner packet with an unchanged
outer factor before recurring on the resulting outer brackets.

The Hall-Petresco packet is instantiated at support bound zero, so it supplies
a correction packet for every atomic inner factor without additional side
conditions.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open CEWord

namespace IBWork

/-- A cutoff Hall-Petresco packet supplies an adjacent correction everywhere. -/
noncomputable def correctionPacket
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (left right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    TSPkt n left right :=
  ((packet.supportedWordFactory
      (WBForm.chooseNormalizerFamily
        (concreteBasicCommutators.{u} d))
      0).correctionPacketFactory).packet
    left right (Nat.zero_le _) (Nat.zero_le _)

/--
Exact signed-polynomial source for the bracket of one concrete inner-reduction
packet with an unchanged outer-right factor.
-/
noncomputable def factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SBWork.factors right
    (correctionPacket packet · right)
    (basicReductionFactors inner)

/--
The concrete inner-packet worklist evaluates exactly to the outer bracket of
the atomic Hall-reduction packet and the unchanged right factor.
-/
theorem listEval_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (factors packet inner right) =
      ⁅SPFactor.listEval (n := n) e
          (basicReductionFactors inner),
        right.eval (n := n) e⁆ :=
  SBWork.listEval_factors right
    (correctionPacket packet · right) e
      (basicReductionFactors inner)

/-- The concrete worklist retains the lower support bound of the inner packet. -/
theorem weight_least_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    SPFactor.WordWeightLeast
      (inner.word.weight HEAddres.weight)
      (factors packet inner right) :=
  SBWork.weight_least_factors
    right (correctionPacket packet · right)
      (least_reduction_factors inner)

/-- Truncating the inner factor physically truncates its outer-bracket worklist. -/
theorem isTruncated_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (factors packet inner right) :=
  SBWork.isTruncated_factors right
    (correctionPacket packet · right)
      (truncated_reduction_factors inner hinnerTruncated)

end IBWork
end TCTex
end Submission

/-!
# Exact reconstruction worklists for polynomial inner-span branches

The atomic Hall packet followed by its raw signed residual reconstructs the
original inner factor exactly.  Bracketing that reconstructed source with one
unchanged outer factor gives an exact nonlinear counterpart of the classical
inner-span branch.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open CEWord

namespace IBRecons

/-- The atomic Hall packet followed by its raw residual reconstructs one factor. -/
noncomputable def innerReconstructionSource
    {d : ℕ}
    {ι : Type}
    (inner :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  basicReductionFactors inner ++ basicRawSource inner

/-- The reconstruction source evaluates exactly to the original inner factor. -/
theorem list_inner_reconstruction
    {d n : ℕ}
    {ι : Type}
    (inner :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (innerReconstructionSource inner) =
      inner.eval (n := n) e := by
  rw [innerReconstructionSource, SPFactor.listEval_append,
    reduction_raw_source]
  group

/-- The reconstruction source retains the original inner support bound. -/
theorem least_inner_reconstruction
    {d : ℕ}
    {ι : Type}
    (inner :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    SPFactor.WordWeightLeast
      (inner.word.weight HEAddres.weight)
      (innerReconstructionSource inner) := by
  intro factor hfactor
  simp only [innerReconstructionSource, basicRawSource,
    List.mem_append, List.mem_singleton] at hfactor
  rcases hfactor with hfactor | hfactor | rfl
  · exact least_reduction_factors inner factor hfactor
  · rw [SPFactor.inverseList] at hfactor
    rcases List.mem_map.mp hfactor with ⟨sourceFactor, hsourceFactor, rfl⟩
    simpa only [SPFactor.word_neg] using
      least_reduction_factors inner sourceFactor
        (by simpa using hsourceFactor)
  · exact Nat.le_refl _

/-- Every factor in the reconstruction source has exactly the inner weight. -/
theorem inner_reconstruction_source
    {d : ℕ}
    {ι : Type}
    (inner :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hfactor : factor ∈ innerReconstructionSource inner) :
    factor.word.weight HEAddres.weight =
      inner.word.weight HEAddres.weight := by
  simp only [innerReconstructionSource, basicRawSource,
    List.mem_append, List.mem_singleton] at hfactor
  rcases hfactor with hfactor | hfactor | rfl
  · exact word_reduction_factors inner hfactor
  · rw [SPFactor.inverseList] at hfactor
    rcases List.mem_map.mp hfactor with ⟨sourceFactor, hsourceFactor, rfl⟩
    simpa only [SPFactor.word_neg] using
      word_reduction_factors inner
        (by simpa using hsourceFactor)
  · rfl

/-- Truncating the inner factor truncates its exact reconstruction source. -/
theorem truncated_inner_reconstruction
    {d n : ℕ}
    {ι : Type}
    (inner :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (innerReconstructionSource inner) := by
  intro factor hfactor
  rcases List.mem_append.mp hfactor with hfactor | hfactor
  · exact truncated_reduction_factors inner hinnerTruncated factor hfactor
  · exact
      truncated_reduction_source inner hinnerTruncated
        factor hfactor

/-- Exact outer-bracket worklist for the reconstructed inner source. -/
noncomputable def factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SBWork.factors right
    (IBWork.correctionPacket
      packet · right)
    (innerReconstructionSource inner)

/-- The reconstruction worklist evaluates to the full outer commutator. -/
theorem listEval_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (factors packet inner right) =
      ⁅inner.eval (n := n) e, right.eval (n := n) e⁆ := by
  rw [factors,
    SBWork.listEval_factors,
    list_inner_reconstruction]

/-- The exact worklist and correction packet are evaluation-equivalent. -/
theorem list_factors_packet
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (factors packet inner right) =
      SPFactor.listEval e
        (IBWork.correctionPacket
          packet inner right).factors := by
  rw [listEval_factors,
    (IBWork.correctionPacket
      packet inner right).listEval_eq]

/-- The reconstruction worklist retains the original inner support bound. -/
theorem weight_least_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    SPFactor.WordWeightLeast
      (inner.word.weight HEAddres.weight)
      (factors packet inner right) :=
  SBWork.weight_least_factors
    right
    (IBWork.correctionPacket
      packet · right)
    (least_inner_reconstruction inner)

/-- Truncating the inner factor truncates the reconstruction worklist. -/
theorem isTruncated_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (factors packet inner right) :=
  SBWork.isTruncated_factors right
    (IBWork.correctionPacket
      packet · right)
    (truncated_inner_reconstruction inner hinnerTruncated)

/-- The exact reconstruction worklist lies at full outer-bracket depth. -/
theorem list_series_sub
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (factors packet inner right) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight - 1) := by
  rw [listEval_factors]
  have hindex :
      (inner.word.weight HEAddres.weight - 1) +
            (right.word.weight HEAddres.weight - 1) + 1 =
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight - 1 := by
    have hinnerPos := inner.word_weight_pos
    have hrightPos := right.word_weight_pos
    omega
  simpa only [hindex] using
    element_lower_series
      (inner.eval_lower_series (n := n) e)
      (right.eval_lower_series (n := n) e)

end IBRecons
end TCTex
end Submission

/-!
# Total-weight support for polynomial inner-packet outer brackets

Atomic Hall reduction replaces an arbitrary inner word by factors of exactly
the same weight.  Bracketing each atomic factor with one fixed outer-right
factor therefore emits Hall-Petresco corrections supported at the sum of the
original inner and outer weights.

The exact outer-bracket worklist also retains conjugating copies of the
atomic factors.  This file isolates its genuinely descending terminal
correction source from those wrappers.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace IBWork

/-- Every retained adjacent correction has the sum of its two parent weights. -/
theorem add_packet_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (left right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hfactor :
      factor ∈ (correctionPacket packet left right).factors) :
    left.word.weight HEAddres.weight +
        right.word.weight HEAddres.weight ≤
      factor.word.weight HEAddres.weight := by
  change
    factor ∈
      SPFactor.truncate n
        (PFSubsti.symbolicFactors
          ((WBForm.chooseNormalizerFamily
            (concreteBasicCommutators.{u} d)).normalizer ι)
          packet.recipes left right) at hfactor
  have hfactor' := (List.mem_filter.mp hfactor).1
  rcases
      PFSubsti.recipe_factors
        hfactor' with
    ⟨recipe, _hrecipe, rfl⟩
  rw [PFSubsti.word_symbolic_factor]
  have hleft :=
    BRSpec.leftDegree_pos recipe
  have hright :=
    BRSpec.rightDegree_pos recipe
  exact
    Nat.add_le_add
      (Nat.le_mul_of_pos_left _ hleft)
      (Nat.le_mul_of_pos_left _ hright)

/--
Flatten only the terminal Hall-Petresco corrections in the exact outer
bracket worklist, omitting retained conjugating copies.
-/
noncomputable def terminalCorrectionFactors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  (basicReductionFactors inner).flatMap fun left =>
    (correctionPacket packet left right).factors

/-- Terminal corrections are supported at the outer total weight. -/
theorem least_terminal_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    SPFactor.WordWeightLeast
      (inner.word.weight HEAddres.weight +
        right.word.weight HEAddres.weight)
      (terminalCorrectionFactors packet inner right) := by
  intro factor hfactor
  rw [terminalCorrectionFactors] at hfactor
  rcases List.mem_flatMap.mp hfactor with ⟨left, hleft, hfactor⟩
  have hleftWeight :=
    word_reduction_factors inner hleft
  simpa only [hleftWeight] using
    add_packet_factors
      packet left right hfactor

/-- Terminal corrections are physically below the truncation cutoff. -/
theorem truncated_terminal_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    SPFactor.IsTruncated n
      (terminalCorrectionFactors packet inner right) := by
  intro factor hfactor
  rw [terminalCorrectionFactors] at hfactor
  rcases List.mem_flatMap.mp hfactor with ⟨left, _hleft, hfactor⟩
  exact
    (correctionPacket packet left right).word_weight_cutoff
      factor hfactor

end IBWork
end TCTex
end Submission

/-!
# Direct normalization of concrete polynomial outer-bracket corrections

The Hall-Petresco correction packet attached to an inner factor and an
outer-right factor is physically supported at their total bracket weight.
Consequently, normalizers strictly above the inner factor normalize that
packet directly at total weight.  No reconstruction wrappers or same-stratum
normalizer are needed for this packet-facing endpoint.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open TPSem

namespace IBWork

/-- The concrete correction packet admits direct total-weight normalization. -/
lemma nonempty_normalization_total
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d)) :
    Nonempty
      (TPSem
        (inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight - 1)
        (correctionPacket packet inner right)) := by
  let totalWeight :=
    inner.word.weight HEAddres.weight +
      right.word.weight HEAddres.weight
  have htotalWeightPos : 1 ≤ totalWeight := by
    have hinnerPos := inner.word_weight_pos
    omega
  let C := correctionPacket packet inner right
  rcases
      (normalizerAbove totalWeight (by
        have hrightPos := right.word_weight_pos
        omega)).normalize C.factors C.isTruncated_factors
          (by
            intro factor hfactor
            exact
              add_packet_factors
                packet inner right hfactor) with
    ⟨coordinates, hcoordinates, heval⟩
  exact
    ⟨{
      coordinates := coordinates
      coordinates_no_below := by
        simpa only [totalWeight, Nat.sub_add_cancel htotalWeightPos] using
          hcoordinates
      list_eval_coordinates := fun e => (heval e).trans (C.listEval_eq e)
    }⟩

/-- Choose the directly normalized correction packet at total bracket weight. -/
noncomputable def normalization_normalizer_above
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d)) :
    TPSem
      (inner.word.weight HEAddres.weight +
        right.word.weight HEAddres.weight - 1)
      (correctionPacket packet inner right) :=
  Classical.choice
    (nonempty_normalization_total
      packet inner right normalizerAbove)

/-- Expose direct total-weight normalization sharply above the inner parent. -/
noncomputable def
    sharp_above_total
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d)) :
    TPSem
      (inner.word.weight HEAddres.weight)
      (correctionPacket packet inner right) :=
  (normalization_normalizer_above
    packet inner right normalizerAbove).weaken (by
      have hrightPos := right.word_weight_pos
      omega)

/-- Replacing the inner parent by its direct sharp correction endpoint descends. -/
lemma
    normalization_total_multiset
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (P :
      List
        (SPFactor
          (concreteBasicCommutators.{u} d) ι)) :
    SPFactor.CutoffDefectMultiset n
      (P ++
        (sharp_above_total
          packet inner right normalizerAbove).coordinates.factors (n := n))
      (P ++ [inner]) :=
  multisetAppendSingleton
    (sharp_above_total
      packet inner right normalizerAbove)
    P

end IBWork

end TCTex
end Submission

/-!
# Recursive inventory of concrete polynomial inner-packet outer brackets

The exact outer-bracket worklist retains same-stratum wrappers around its
recursive tail, while every terminal Hall-Petresco correction is supported
strictly above either parent.  This file packages that split for the concrete
atomic inner-reduction packet.

This is the finite source-level interface needed to combine outer Hall-rank
recursion for atomic brackets with ordinary weight recursion for correction
terms.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace IBWork

/-- Every concrete worklist factor is a wrapper or a terminal correction. -/
theorem or_terminal_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ factors packet inner right) :
    (∃ left ∈ basicReductionFactors inner, x = left) ∨
      (∃ left ∈ basicReductionFactors inner, x = left.neg) ∨
        x ∈ terminalCorrectionFactors packet inner right := by
  rcases
      SBWork.left_or_factors
        right (correctionPacket packet · right) hx with
    hleft | hleft | hcorrection
  · exact Or.inl hleft
  · exact Or.inr (Or.inl hleft)
  · rcases hcorrection with ⟨left, hleft, hfactor⟩
    exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨left, hleft, hfactor⟩))

/-- Terminal corrections have weight strictly above the inner packet. -/
theorem inner_terminal_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hfactor :
      factor ∈ terminalCorrectionFactors packet inner right) :
    inner.word.weight HEAddres.weight <
      factor.word.weight HEAddres.weight := by
  have htotal :=
    least_terminal_factors
      packet inner right factor hfactor
  have hrightPos := right.word_weight_pos
  omega

/-- Terminal corrections have weight strictly above the outer-right factor. -/
theorem right_terminal_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hfactor :
      factor ∈ terminalCorrectionFactors packet inner right) :
    right.word.weight HEAddres.weight <
      factor.word.weight HEAddres.weight := by
  have htotal :=
    least_terminal_factors
      packet inner right factor hfactor
  have hinnerPos := inner.word_weight_pos
  omega

/--
Every concrete worklist factor is an atomic wrapper or is strictly heavier
than the original inner packet.
-/
theorem or_neg_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ factors packet inner right) :
    (∃ left ∈ basicReductionFactors inner, x = left ∨ x = left.neg) ∨
      inner.word.weight HEAddres.weight <
        x.word.weight HEAddres.weight := by
  rcases
      or_terminal_factors
        packet inner right hx with
    hleft | hleft | hcorrection
  · rcases hleft with ⟨left, hleft, hxleft⟩
    exact Or.inl ⟨left, hleft, Or.inl hxleft⟩
  · rcases hleft with ⟨left, hleft, hxleft⟩
    exact Or.inl ⟨left, hleft, Or.inr hxleft⟩
  · exact
      Or.inr
        (inner_terminal_factors
          packet inner right hcorrection)

end IBWork
end TCTex
end Submission

/-!
# Support of polynomial reconstruction-worklist residuals

Replacing an inner signed-polynomial factor by its canonical atomic packet
and then bracketing with a fixed right factor produces an atomic outer
worklist.  The exact reconstruction worklist has the same outer bracket after
restoring the inner basic-reduction residual.

Their quotient lies one layer above the full outer-bracket weight.  At the
next-stratum cutoff, this residual recollects to the empty source.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

open CEWord
open IBWork
open SBWork

namespace IBRecons

/--
Raw quotient from the atomic outer worklist to the exact reconstruction
worklist.
-/
noncomputable def residualRawSource
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList
      (IBWork.factors packet
        inner right) ++
    factors packet inner right

/-- Evaluation of the raw residual is outer-worklist division. -/
theorem list_raw_source
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (residualRawSource packet inner right) =
      (SPFactor.listEval e
        (IBWork.factors packet
          inner right))⁻¹ *
        SPFactor.listEval e
          (factors packet inner right) := by
  simp [residualRawSource, SPFactor.list_eval_inverse]

/--
The reconstruction residual lies one lower-central layer above the full
outer-bracket weight.
-/
theorem raw_series_add
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (residualRawSource packet inner right) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight) := by
  rw [list_raw_source,
    IBWork.listEval_factors,
    listEval_factors]
  let G := LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
  let atomic : G :=
    SPFactor.listEval (n := n) e
      (basicReductionFactors inner)
  let original : G := inner.eval (n := n) e
  let rightValue : G := right.eval (n := n) e
  let innerWeight := inner.word.weight HEAddres.weight
  let rightWeight := right.word.weight HEAddres.weight
  let K := Subgroup.lowerCentralSeries G (innerWeight + rightWeight)
  change ⁅atomic, rightValue⁆⁻¹ * ⁅original, rightValue⁆ ∈ K
  have hinner :
      atomic⁻¹ * original ∈ Subgroup.lowerCentralSeries G innerWeight := by
    simpa [G, atomic, original, innerWeight] using
      (reduction_inv_series
        (n := n) inner e)
  have hright :
      rightValue ∈ Subgroup.lowerCentralSeries G (rightWeight - 1) := by
    simpa [G, rightValue, rightWeight] using
      (right.eval_lower_series (n := n) e)
  have hinnerReverse :
      atomic * original⁻¹ ∈ Subgroup.lowerCentralSeries G innerWeight := by
    let L := Subgroup.lowerCentralSeries G innerWeight
    have hconj :
        atomic * (atomic⁻¹ * original) * atomic⁻¹ ∈ L :=
      (inferInstance : L.Normal).conj_mem
        (atomic⁻¹ * original) (by simpa [L] using hinner) atomic
    have hinv := L.inv_mem hconj
    have heq :
        (atomic * (atomic⁻¹ * original) * atomic⁻¹)⁻¹ =
          atomic * original⁻¹ := by
      group
    simpa only [heq] using hinv
  have hcomm :
      ⁅atomic, rightValue⁆ * ⁅original, rightValue⁆⁻¹ ∈
        Subgroup.lowerCentralSeries G (innerWeight + (rightWeight - 1) + 1) :=
    congr_inv_series
      hinnerReverse hright
  have hindex :
      innerWeight + (rightWeight - 1) + 1 = innerWeight + rightWeight := by
    have hrightPos := right.word_weight_pos
    simp only [rightWeight]
    omega
  have hcommK :
      ⁅atomic, rightValue⁆ * ⁅original, rightValue⁆⁻¹ ∈ K := by
    simpa only [K, hindex] using hcomm
  have hcommInv :
      ⁅original, rightValue⁆ * ⁅atomic, rightValue⁆⁻¹ ∈ K := by
    have hinv := K.inv_mem hcommK
    have heq :
        (⁅atomic, rightValue⁆ * ⁅original, rightValue⁆⁻¹)⁻¹ =
          ⁅original, rightValue⁆ * ⁅atomic, rightValue⁆⁻¹ := by
      group
    simpa only [heq] using hinv
  have hconj :
      ⁅atomic, rightValue⁆⁻¹ *
            (⁅original, rightValue⁆ * ⁅atomic, rightValue⁆⁻¹) *
          (⁅atomic, rightValue⁆⁻¹)⁻¹ ∈ K :=
    (inferInstance : K.Normal).conj_mem
      (⁅original, rightValue⁆ * ⁅atomic, rightValue⁆⁻¹) hcommInv
        ⁅atomic, rightValue⁆⁻¹
  have heq :
      ⁅atomic, rightValue⁆⁻¹ *
            (⁅original, rightValue⁆ * ⁅atomic, rightValue⁆⁻¹) *
          (⁅atomic, rightValue⁆⁻¹)⁻¹ =
        ⁅atomic, rightValue⁆⁻¹ * ⁅original, rightValue⁆ := by
    group
  simpa only [heq] using hconj

/-- The reconstruction residual is trivial once its next layer is cut off. -/
theorem n_succ_add
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hcutoff :
      n ≤
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight + 1)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (residualRawSource packet inner right) =
      1 := by
  apply eq_bot_iff.mp
    SCFactor.trunc_last_bot
  exact Subgroup.lowerCentralSeries_antitone (by omega)
    (raw_series_add
      packet inner right e)

/--
At the next-stratum cutoff, the reconstruction residual recollects to the
empty source at any requested support bound.
-/
def recollection_terminal
    {d n lowerWeight : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (hcutoff :
      n ≤
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight + 1) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight)
      (concreteBasicCommutators.{u} d)
      (residualRawSource packet inner right) where
  higherSource := []
  higher_source_truncated := by
    intro x hx
    simp at hx
  higher_weight_least := by
    intro x hx
    simp at hx
  list_higher_raw := by
    intro e
    simpa using
      (n_succ_add
        packet inner right hcutoff e).symm

end IBRecons
end TCTex
end Submission

/-!
# Ranked recursive inventory of concrete polynomial inner-packet outer brackets

The exact inner-packet outer-bracket worklist has a lexicographic recursive
shape.  Its terminal Hall-Petresco corrections increase ordinary word weight.
Its same-weight wrappers come from atomic Hall reduction, and bracketing those
atoms with the unchanged outer tree strictly decreases the fixed-weight Hall
rank defect.

This file combines the two progress arguments into one source-level theorem.
It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace IBWork

/--
Every exact worklist factor either comes from a same-weight atomic wrapper
whose outer bracket has smaller Hall-rank defect, or increases ordinary word
weight.
-/
theorem ranked_or_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ factors packet inner right)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    (∃ left ∈ basicReductionFactors inner,
      (x = left ∨ x = left.neg) ∧
        HallTree.bracketRankDefect
            ((tree inner.word).weight + unchanged.weight)
            (tree x.word) unchanged <
          HallTree.bracketRankDefect
            ((tree inner.word).weight + unchanged.weight)
            originalLeft originalRight) ∨
      inner.word.weight HEAddres.weight <
        x.word.weight HEAddres.weight := by
  rcases
      or_neg_factors
        packet inner right hx with
    hleft | hhigher
  · rcases hleft with ⟨left, hleft, hxleft⟩
    rcases hxleft with hxleft | hxleft
    · exact
        hxleft ▸ Or.inl
          ⟨left, hleft, Or.inl rfl,
            bracket_defect_factors
              inner hleft added originalRight unchanged originalLeft
                hinnerTree hRightLeft hRightUnchanged hunchangedBasic⟩
    · exact
        hxleft ▸ Or.inl
          ⟨left, hleft, Or.inr rfl, by
            simpa only [SPFactor.word_neg] using
              (bracket_defect_factors
                inner hleft added originalRight unchanged originalLeft
                  hinnerTree hRightLeft hRightUnchanged hunchangedBasic)⟩
  · exact Or.inr hhigher

end IBWork
end TCTex
end Submission

/-!
# Lexicographic descent for concrete polynomial inner-packet outer brackets

Unrestricted symbolic Hall collection needs two recursion measures.  A
Hall-Petresco terminal correction strictly increases ordinary word weight,
so its cutoff defect decreases.  An atomic wrapper retains the original
inner weight, but its outer Hall bracket has strictly smaller reverse finite
rank defect.

This file packages the lexicographic product of those measures and proves
that every factor emitted by a concrete inner-packet outer-bracket worklist
descends.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SPFactor

/-- Cutoff defect followed by fixed-weight Hall-bracket rank defect. -/
def hallRankedMeasure
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (factor : SPFactor H ι)
    (rankDefect : ℕ) :
    ℕ × ℕ :=
  (cutoffDefect n factor, rankDefect)

/-- Lexicographic descent for one symbolic Hall task. -/
def HallRankedDescends
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (n : ℕ)
    (child : SPFactor H ι)
    (childRankDefect : ℕ)
    (parent : SPFactor H ι)
    (parentRankDefect : ℕ) :
    Prop :=
  Prod.Lex (· < ·) (· < ·)
    (hallRankedMeasure n child childRankDefect)
    (hallRankedMeasure n parent parentRankDefect)

/-- Hall-ranked descent is well-founded because both components are naturals. -/
lemma descends_well_founded
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type} :
    WellFounded
      (fun child parent : SPFactor H ι × ℕ =>
        HallRankedDescends n child.1 child.2 parent.1 parent.2) := by
  unfold HallRankedDescends
  exact
    InvImage.wf
      (fun task : SPFactor H ι × ℕ =>
        hallRankedMeasure n task.1 task.2)
      (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)

/-- Recursion principle for cutoff-defect/Hall-rank symbolic tasks. -/
theorem ranked_descends_induction
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    {motive : SPFactor H ι → ℕ → Prop}
    (step :
      ∀ parent parentRankDefect,
        (∀ child childRankDefect,
          HallRankedDescends n child childRankDefect parent parentRankDefect →
            motive child childRankDefect) →
          motive parent parentRankDefect)
    (factor : SPFactor H ι)
    (rankDefect : ℕ) :
    motive factor rankDefect := by
  refine
    (descends_well_founded (n := n)).induction
      (C := fun task => motive task.1 task.2)
        (factor, rankDefect) ?_
  intro task ih
  exact step task.1 task.2 fun child childRankDefect hdescends =>
    ih (child, childRankDefect) hdescends

/-- A strict ordinary word-weight rise decreases the first measure component. -/
lemma ranked_descends_weight
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (child parent : SPFactor H ι)
    (childRankDefect parentRankDefect : ℕ)
    (hparentTruncated :
      parent.word.weight HEAddres.weight < n)
    (hweight :
      parent.word.weight HEAddres.weight <
        child.word.weight HEAddres.weight) :
    HallRankedDescends n child childRankDefect parent parentRankDefect := by
  apply Prod.Lex.left
  simp only [cutoffDefect]
  omega

/-- At fixed ordinary weight, strict Hall-rank progress decreases the second component. -/
lemma ranked_descends_defect
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (child parent : SPFactor H ι)
    (childRankDefect parentRankDefect : ℕ)
    (hweight :
      child.word.weight HEAddres.weight =
        parent.word.weight HEAddres.weight)
    (hrank : childRankDefect < parentRankDefect) :
    HallRankedDescends n child childRankDefect parent parentRankDefect := by
  simpa only [HallRankedDescends, hallRankedMeasure, cutoffDefect, hweight] using
    (Prod.Lex.right
      (n - parent.word.weight HEAddres.weight) hrank)

end SPFactor

namespace IBWork

open CEWord

/--
Every factor emitted by one concrete inner-packet outer-bracket worklist
strictly descends in cutoff-defect/Hall-rank lexicographic order.
-/
theorem ranked_descends_factors
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ factors packet inner right)
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactor.HallRankedDescends n x
      (HallTree.bracketRankDefect
        ((tree inner.word).weight + unchanged.weight)
        (tree x.word) unchanged)
      inner
      (HallTree.bracketRankDefect
        ((tree inner.word).weight + unchanged.weight)
        originalLeft originalRight) := by
  rcases
      ranked_or_factors
        packet inner right hx added originalRight unchanged originalLeft
          hinnerTree hRightLeft hRightUnchanged hunchangedBasic with
    hwrapped | hhigher
  · rcases hwrapped with ⟨left, hleft, hxleft, hrank⟩
    have hleftWeight :=
      word_reduction_factors inner hleft
    apply
      SPFactor.ranked_descends_defect
    · rcases hxleft with hxleft | hxleft
      · simpa only [hxleft] using hleftWeight
      · simpa only [hxleft, SPFactor.word_neg] using
          hleftWeight
    · exact hrank
  · exact
      SPFactor.ranked_descends_weight
        x inner _ _ hinnerTruncated hhigher

end IBWork
end TCTex
end Submission

/-!
# Signed-polynomial full outer children from inner Hall reduction

Reducing an inner expanded Hall tree while retaining the fixed outer word
gives a finite packet of full-weight signed-polynomial children.  Each child
keeps the original formula and scales it by the corresponding inner Hall
coordinate.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace SPFactor

/-- Multiply only the signed formula of a symbolic factor by an integer. -/
def coefficientScale
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (coefficient : ℤ) :
    SPFactor H ι where
  word := factor.word
  coefficient := factor.coefficient.scale coefficient

@[simp]
theorem word_coefficientScale
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (coefficient : ℤ) :
    (factor.coefficientScale coefficient).word = factor.word :=
  rfl

@[simp]
theorem coefficient_eval_scale
    {d : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (factor : SPFactor H ι)
    (coefficient : ℤ)
    (e : ι → HEFam H) :
    (factor.coefficientScale coefficient).coefficient.eval e =
      coefficient * factor.coefficient.eval e := by
  simp [coefficientScale]

end SPFactor

namespace CEWord

/-- One full outer child `[basic_i, right]` with a scaled signed formula. -/
noncomputable def innerOuterFactor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight) :
    SPFactor
      (concreteBasicCommutators.{u} d) ι :=
  (factor.reword
      (.commutator (.atom (basicReductionAddress i)) rightWord)
      (by
        rw [hword]
        simp only [CWord.weight_commutator, CWord.weight_atom,
          basic_reduction_address, tree_weight]))
    |>.coefficientScale (HallTree.basicReductionCoordinates (tree innerWord) i)

@[simp]
theorem inner_reduction_factor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight) :
    (innerOuterFactor factor innerWord rightWord hword i).word =
      .commutator (.atom (basicReductionAddress i)) rightWord := by
  simp [innerOuterFactor]

@[simp]
theorem coefficient_inner_factor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (innerOuterFactor factor innerWord rightWord hword i).coefficient.eval
        e =
      HallTree.basicReductionCoordinates (tree innerWord) i *
        factor.coefficient.eval e := by
  rw [innerOuterFactor,
    SPFactor.coefficient_eval_scale,
    SPFactor.coefficient_eval_reword]

@[simp]
theorem inner_outer_factor
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight) :
    (innerOuterFactor factor innerWord rightWord hword i).word.weight
        HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  rw [inner_reduction_factor, hword]
  simp only [CWord.weight_commutator, CWord.weight_atom,
    basic_reduction_address, tree_weight]

/-- Ordered full-weight outer children emitted by inner Hall reduction. -/
noncomputable def innerOuterFactors
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  (Finset.univ.sort
      fun i j :
        HallTree.BasicIndex
          (α := FreeGenerator.{u} d) (tree innerWord).weight =>
        i ≤ j).map
    (innerOuterFactor factor innerWord rightWord hword)

/-- Membership in the outer-child packet preserves the original full weight. -/
theorem inner_outer_factors
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    {x :
      SPFactor
        (concreteBasicCommutators.{u} d) ι}
    (hx : x ∈ innerOuterFactors factor innerWord rightWord hword) :
    x.word.weight HEAddres.weight =
      factor.word.weight HEAddres.weight := by
  rw [innerOuterFactors] at hx
  rcases List.mem_map.mp hx with ⟨i, _hi, rfl⟩
  exact inner_outer_factor factor innerWord rightWord hword i

/-- Full outer children inherit physical truncation from their parent. -/
theorem truncated_inner_factors
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactor : factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (innerOuterFactors factor innerWord rightWord hword) := by
  intro x hx
  rw [inner_outer_factors
    factor innerWord rightWord hword hx]
  exact hfactor

/-- Every full outer child remains supported in the parent stratum. -/
theorem least_inner_factors
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    SPFactor.WordWeightLeast
      (factor.word.weight HEAddres.weight)
      (innerOuterFactors factor innerWord rightWord hword) := by
  intro x hx
  rw [inner_outer_factors
    factor innerWord rightWord hword hx]

@[simp]
theorem
    truncation_indexed_rep
    {d n : ℕ}
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight) :
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (HallTree.indexedInnerRep
          (tree innerWord) (tree rightWord) i) =
      (CWord.commutator
        (.atom (basicReductionAddress i)) rightWord).eval
        HEAddres.freeLowerTruncation := by
  rw [← lower_truncation_tree
    (CWord.commutator (.atom (basicReductionAddress i)) rightWord)]
  congr 1
  simp only [HallTree.indexedInnerRep,
    HallTree.coe_rep_weight, tree_commutator, tree_atom,
    basicReductionAddress, concreteBasicTree]

/-- Evaluation of one recipe-correct full outer child. -/
@[simp]
theorem inner_reduction_eval
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (i :
      HallTree.BasicIndex
        (α := FreeGenerator.{u} d) (tree innerWord).weight)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (innerOuterFactor factor innerWord rightWord hword i).eval
        (n := n) e =
      ((CWord.commutator
          (.atom (basicReductionAddress i)) rightWord).eval
          HEAddres.freeLowerTruncation) ^
        (HallTree.basicReductionCoordinates (tree innerWord) i *
          factor.coefficient.eval e) := by
  rw [SPFactor.eval,
    coefficient_inner_factor]
  rfl

/-- Truncation carries the HallBasic outer-child product to symbolic values. -/
theorem truncation_inner_scaled
    {d n : ℕ}
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (z : ℤ) :
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (HallTree.innerOuterScaled
          (tree innerWord) (tree rightWord) z) =
      ((Finset.univ.sort
          fun i j :
            HallTree.BasicIndex
              (α := FreeGenerator.{u} d) (tree innerWord).weight =>
            i ≤ j).map
        fun i =>
          ((CWord.commutator
              (.atom (basicReductionAddress i)) rightWord).eval
              HEAddres.freeLowerTruncation) ^
            (HallTree.basicReductionCoordinates (tree innerWord) i * z)).prod := by
  simp only [HallTree.innerOuterScaled,
    HallTree.innerScaledTerm]
  let indices :=
    Finset.univ.sort
      fun i j :
        HallTree.BasicIndex
          (α := FreeGenerator.{u} d) (tree innerWord).weight =>
        i ≤ j
  change
    lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (((indices.map fun i =>
          HallTree.indexedInnerRep
              (tree innerWord) (tree rightWord) i ^
            (HallTree.basicReductionCoordinates (tree innerWord) i * z)).prod :
          Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d))
            ((tree innerWord).weight + (tree rightWord).weight - 1)) :
          FreeGroup (FreeGenerator.{u} d)) =
      (indices.map fun i =>
        ((CWord.commutator
            (.atom (basicReductionAddress i)) rightWord).eval
            HEAddres.freeLowerTruncation) ^
          (HallTree.basicReductionCoordinates (tree innerWord) i * z)).prod
  induction indices with
  | nil =>
      simp
  | cons i indices ih =>
      simp only [List.map_cons, List.prod_cons]
      change
        lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
            ((HallTree.indexedInnerRep
                (tree innerWord) (tree rightWord) i :
                FreeGroup (FreeGenerator.{u} d)) ^
              (HallTree.basicReductionCoordinates (tree innerWord) i * z) *
              (((indices.map fun j =>
                HallTree.indexedInnerRep
                    (tree innerWord) (tree rightWord) j ^
                  (HallTree.basicReductionCoordinates (tree innerWord) j * z)).prod :
                Subgroup.lowerCentralSeries (FreeGroup (FreeGenerator.{u} d))
                  ((tree innerWord).weight + (tree rightWord).weight - 1)) :
                FreeGroup (FreeGenerator.{u} d))) =
          ((CWord.commutator
              (.atom (basicReductionAddress i)) rightWord).eval
                HEAddres.freeLowerTruncation) ^
              (HallTree.basicReductionCoordinates (tree innerWord) i * z) *
            (indices.map fun j =>
              ((CWord.commutator
                  (.atom (basicReductionAddress j)) rightWord).eval
                  HEAddres.freeLowerTruncation) ^
                (HallTree.basicReductionCoordinates (tree innerWord) j * z)).prod
      rw [map_mul, map_zpow,
        truncation_indexed_rep,
        ih]

/-- The outer-child packet evaluates to the truncated HallBasic product. -/
theorem inner_reduction_factors
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (innerOuterFactors factor innerWord rightWord hword) =
      lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n
        (HallTree.innerOuterScaled
          (tree innerWord) (tree rightWord) (factor.coefficient.eval e)) := by
  rw [truncation_inner_scaled]
  unfold SPFactor.listEval innerOuterFactors
  rw [List.map_map]
  induction
      (Finset.univ.sort
        fun i j :
          HallTree.BasicIndex
            (α := FreeGenerator.{u} d) (tree innerWord).weight =>
          i ≤ j) with
  | nil =>
      rfl
  | cons i indices ih =>
      simp only [List.map_cons, List.prod_cons, Function.comp_apply]
      rw [inner_reduction_eval, ih]

/-- Raw residual: invert the full-weight children and append the parent. -/
noncomputable def innerRawSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    List
      (SPFactor
        (concreteBasicCommutators.{u} d) ι) :=
  SPFactor.inverseList
      (innerOuterFactors factor innerWord rightWord hword) ++
    [factor]

/-- The raw outer-child residual source inherits physical truncation. -/
theorem truncated_inner_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactor : factor.word.weight HEAddres.weight < n) :
    SPFactor.IsTruncated n
      (innerRawSource
        factor innerWord rightWord hword) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact
      SPFactor.truncated_inverse_list
        (truncated_inner_factors
          factor innerWord rightWord hword hfactor) x hx
  · simp only [List.mem_singleton] at hx
    subst x
    exact hfactor

/-- The raw residual remains physically in the parent stratum. -/
theorem outerResidualSource
    {d : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord) :
    SPFactor.WordWeightLeast
      (factor.word.weight HEAddres.weight)
      (innerRawSource
        factor innerWord rightWord hword) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · rw [SPFactor.inverseList] at hx
    rcases List.mem_map.mp hx with ⟨child, hchild, rfl⟩
    rw [SPFactor.word_neg]
    exact
      least_inner_factors
        factor innerWord rightWord hword child (by simpa using hchild)
  · simp only [List.mem_singleton] at hx
    subst x
    exact Nat.le_refl _

/-- The raw source evaluates to child-packet division by the parent. -/
theorem inner_raw_source
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (innerRawSource
          factor innerWord rightWord hword) =
      (SPFactor.listEval e
        (innerOuterFactors factor innerWord rightWord hword))⁻¹ *
          factor.eval e := by
  simp [innerRawSource,
    SPFactor.list_eval_inverse]

/-- Dividing by the full-weight child packet leaves a deeper value. -/
theorem
    inner_inv_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    (SPFactor.listEval (n := n) e
        (innerOuterFactors factor innerWord rightWord hword))⁻¹ *
          factor.eval e ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  have hfree :=
    HallTree.inner_scaled_zpow
      (tree innerWord) (tree rightWord) (factor.coefficient.eval e)
  have hmap :=
    Subgroup.lowerCentralSeries.map
      (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
      (factor.word.weight HEAddres.weight)
      (Subgroup.mem_map_of_mem
        (lowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (by
          rw [hword]
          simpa only [tree_weight, HallTree.weight_commutator,
            CWord.weight_commutator] using hfree))
  rw [inner_reduction_factors]
  rw [map_mul, map_inv, map_zpow,
    ← tree_commutator innerWord rightWord,
    lower_truncation_tree] at hmap
  simpa only [SPFactor.eval,
    SPFactor.wordValue, hword] using hmap

/-- The concrete raw residual evaluates one stratum deeper. -/
theorem
    inner_reduction_series
    {d n : ℕ}
    {ι : Type}
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (innerRawSource
          factor innerWord rightWord hword) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (factor.word.weight HEAddres.weight) := by
  rw [inner_raw_source]
  exact
    inner_inv_series
      factor innerWord rightWord hword e

end CEWord
end TCTex
end Submission

/-!
# Structural recollection with directly normalized terminal corrections

The generic outer-bracket worklist recursion appends each terminal correction
packet as a raw higher source.  For the concrete Hall-Petresco packet, the
terminal correction can instead be normalized immediately at total bracket
weight.  Wrapper conjugations still use the ordinary sharp higher-tail router.

This file packages that mixed route and specializes it to concrete inner
basic-reduction packets.  It is intentionally not imported by the existing
collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace SBWork

/--
Structurally recollect an outer-bracket worklist while replacing every terminal
correction packet by a supplied signed semantic normalization.
-/
noncomputable def
    recollect_sharp_normalizer
    {d n lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (factory :
      TSFtry
        (n := n) H lowerWeight)
    (sharp :
      TSNormala
        (n := n) (lowerWeight := lowerWeight) H)
    (right : SPFactor H ι)
    (packet :
      ∀ left : SPFactor H ι,
        TSPkt n left right)
    (terminalNormalization :
      ∀ left : SPFactor H ι,
        left.word.weight HEAddres.weight = lowerWeight →
          TPSem
            lowerWeight (packet left)) :
    ∀ left : List (SPFactor H ι),
      SPFactor.IsTruncated n left →
        (∀ x ∈ left,
          x.word.weight HEAddres.weight = lowerWeight) →
          SSRecol
            (n := n) (lowerWeight := lowerWeight + 1) H
            (factors right packet left)
  | [], _hleftTruncated, _hleftWeight =>
      SSRecol.empty
  | head :: tail, hleftTruncated, hleftWeight => by
      have hheadTruncated :
          head.word.weight HEAddres.weight < n :=
        hleftTruncated head (by simp)
      have htailTruncated :
          SPFactor.IsTruncated n tail := by
        intro x hx
        exact hleftTruncated x (by simp [hx])
      have hheadWeight :
          head.word.weight HEAddres.weight = lowerWeight :=
        hleftWeight head (by simp)
      have htailWeight :
          ∀ x ∈ tail,
            x.word.weight HEAddres.weight = lowerWeight := by
        intro x hx
        exact hleftWeight x (by simp [hx])
      let tailRecollection :=
        recollect_sharp_normalizer
          factory sharp right packet terminalNormalization tail htailTruncated
            htailWeight
      let conjugated :=
        factory.conjugated_recollection_normalizer sharp
          head.neg
          (by simpa only [SPFactor.word_neg] using
            hheadWeight)
          (by simpa only [SPFactor.word_neg] using
            hheadTruncated)
          (factors right packet tail)
          tailRecollection.higherSource
          tailRecollection.higher_source_truncated
          tailRecollection.higher_weight_least
          tailRecollection.list_higher_raw
      let terminal := terminalNormalization head hheadWeight
      exact
        {
          higherSource :=
            conjugated.higherSource ++ terminal.coordinates.factors (n := n)
          higher_source_truncated := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact conjugated.higher_source_truncated x hx
            · exact terminal.factors_isTruncated x hx
          higher_weight_least := by
            intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact conjugated.higher_least_succ x hx
            · exact terminal.weight_least_succ x hx
          list_higher_raw := by
            intro e
            rw [SPFactor.listEval_append,
              conjugated.higher_conjugated_raw,
              terminal.list_eval_coordinates]
            simp only [factors_cons,
              SPFactor.conjugatedRawSource,
              SPFactor.listEval_append,
              SPFactor.listEval_cons,
              SPFactor.listEval_nil, mul_one,
              SPFactor.eval_neg, inv_inv,
              (packet head).listEval_eq]
        }

end SBWork
export SBWork
  (recollect_sharp_normalizer)

open SBWork

namespace IBWork

/--
Recollect the concrete inner-packet outer-bracket worklist while immediately
normalizing each terminal Hall-Petresco correction at total bracket weight.
-/
noncomputable def
    normalizer_direct_normalization
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n) :
    SSRecol
      (n := n)
      (lowerWeight := inner.word.weight HEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) :=
  recollect_sharp_normalizer
      ((packet.supportedWordFactory
        (WBForm.chooseNormalizerFamily
          (concreteBasicCommutators.{u} d))
        (inner.word.weight HEAddres.weight))
          |>.correctionPacketFactory)
      (TSNormala.ofNormalizerAbove
        normalizerAbove)
      right
      (correctionPacket packet · right)
      (fun left hleftWeight => by
        simpa only [hleftWeight] using
          sharp_above_total
            packet left right
              (fun strongerWeight hstronger =>
                normalizerAbove strongerWeight (by omega)))
      (basicReductionFactors inner)
      (truncated_reduction_factors inner hinnerTruncated)
      (fun _x hx => word_reduction_factors inner hx)

end IBWork
export IBWork
  (sharp_above_total)

end TCTex
end Submission

/-!
# Structural recollection of concrete polynomial inner-packet outer brackets

The generic outer-bracket worklist collector removes retained conjugating
wrappers by structural recursion.  This file specializes that construction to
the atomic Hall packet emitted by concrete basic reduction.

The specialization assumes normalizers only at weights strictly larger than
the inner factor's weight.  It therefore exposes the non-circular adapter
needed by expanded-Jacobi continuation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord
open IBWork
open SBWork

namespace IBWork

/--
Structurally recollect the exact concrete outer-bracket worklist using only
normalizers strictly above the inner factor's Hall-weight stratum.
-/
noncomputable def source_normalizer_above
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n) :
    SSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight HEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) :=
  SBWork.source_recollect_normalizer
    ((packet.supportedWordFactory
      (WBForm.chooseNormalizerFamily
        (concreteBasicCommutators.{u} d))
      (inner.word.weight HEAddres.weight))
        |>.correctionPacketFactory)
    (TSNormala.ofNormalizerAbove
      normalizerAbove)
    right
    (correctionPacket packet · right)
    (basicReductionFactors inner)
    (truncated_reduction_factors inner hinnerTruncated)
    (fun _x hx => word_reduction_factors inner hx)

end IBWork
end TCTex
end Submission

/-!
# Recollecting signed-polynomial inner-reduction outer children

The full-weight outer-child packet has a current-stratum residual whose value
lies one lower-central layer deeper.  A semantic normalizer recollects that
residual into the next support stratum.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

namespace
  TSNormal

/-- Recollect the full outer-child residual into the next support stratum. -/
noncomputable def
    recollection_inner_raw
    {d n lowerWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (normalizer :
      TSNormal
        (n := n) (lowerWeight := lowerWeight)
          (concreteBasicCommutators.{u} d))
    (factor :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (innerWord rightWord :
      CWord
        (HEAddres (concreteBasicCommutators.{u} d)))
    (hword : factor.word = .commutator innerWord rightWord)
    (hfactorWeight :
      factor.word.weight HEAddres.weight = lowerWeight)
    (hlowerWeightPos : 1 ≤ lowerWeight)
    (hlowerWeightTruncated : lowerWeight < n) :
    SSRecol
      (n := n) (lowerWeight := lowerWeight + 1)
      (concreteBasicCommutators.{u} d)
      (CEWord.innerRawSource
        factor innerWord rightWord hword) :=
  normalizer.source_recollection_series hn
    (concreteBasicCommutators.{u} d) hH
    (CEWord.innerRawSource
      factor innerWord rightWord hword)
    hlowerWeightPos hlowerWeightTruncated
    (CEWord.truncated_inner_source
      factor innerWord rightWord hword (by
        rw [hfactorWeight]
        exact hlowerWeightTruncated))
    (by
      rw [← hfactorWeight]
      exact
        CEWord.outerResidualSource
          factor innerWord rightWord hword)
    (fun e => by
      rw [← hfactorWeight]
      exact
        CEWord.inner_reduction_series
          factor innerWord rightWord hword e)

end
  TSNormal
end TCTex
end Submission

/-!
# Direct-terminal recollection of exact reconstruction outer brackets

The exact inner reconstruction source consists entirely of factors at the
inner parent's weight.  The direct-terminal outer-bracket recursion therefore
recollects its complete wrapper worklist one layer upward while normalizing
every concrete terminal Hall-Petresco packet immediately at total weight.

Transport across the exact reconstruction identity gives a packet-facing
source recollection with an explicit cutoff-defect descent witness.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

open CEWord

namespace IBRecons

/--
Recollect the exact reconstruction outer bracket while directly normalizing
each terminal concrete correction packet at total bracket weight.
-/
noncomputable def
    normalizer_direct_normalization
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n) :
    SSRecol
      (n := n)
      (lowerWeight := inner.word.weight HEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) :=
  recollect_sharp_normalizer
      ((packet.supportedWordFactory
        (WBForm.chooseNormalizerFamily
          (concreteBasicCommutators.{u} d))
        (inner.word.weight HEAddres.weight))
          |>.correctionPacketFactory)
      (TSNormala.ofNormalizerAbove
        normalizerAbove)
      right
      (IBWork.correctionPacket
        packet · right)
      (fun left hleftWeight => by
        simpa only [hleftWeight] using
          sharp_above_total
            packet left right
              (fun strongerWeight hstronger =>
                normalizerAbove strongerWeight (by omega)))
      (innerReconstructionSource inner)
      (truncated_inner_reconstruction inner hinnerTruncated)
      (fun _x hx => inner_reconstruction_source inner hx)

/-- The directly recollected exact source still evaluates to the outer bracket. -/
theorem
    direct_terminal_normalization
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (e :
      ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (normalizer_direct_normalization
          packet inner right normalizerAbove hinnerTruncated).higherSource =
      ⁅inner.eval (n := n) e, right.eval (n := n) e⁆ := by
  rw [
    (normalizer_direct_normalization
      packet inner right normalizerAbove
        hinnerTruncated).list_higher_raw,
    listEval_factors]

/--
Transport the direct-terminal reconstruction route back to the concrete
Hall-Petresco correction packet.
-/
noncomputable def
    normalizer_terminal_normalization
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n) :
    SSRecol
      (n := n)
      (lowerWeight := inner.word.weight HEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (IBWork.correctionPacket
        packet inner right).factors :=
  (normalizer_direct_normalization
    packet inner right normalizerAbove hinnerTruncated)
      |>.of_list_eq
        (list_factors_packet packet inner right)

/-- The packet-facing direct-terminal route evaluates to the outer bracket. -/
theorem
    higher_above_terminal
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (e :
      ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (normalizer_terminal_normalization
          packet inner right normalizerAbove hinnerTruncated).higherSource =
      ⁅inner.eval (n := n) e, right.eval (n := n) e⁆ :=
  direct_terminal_normalization
    packet inner right normalizerAbove hinnerTruncated e

/-- Replacing the inner parent by the packet-facing direct route descends. -/
lemma
    recollect_defect_multiset
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (P :
      List
        (SPFactor
          (concreteBasicCommutators.{u} d) ι)) :
    SPFactor.CutoffDefectMultiset n
      (P ++
        (normalizer_terminal_normalization
          packet inner right normalizerAbove hinnerTruncated).higherSource)
      (P ++ [inner]) :=
  (normalizer_terminal_normalization
    packet inner right normalizerAbove hinnerTruncated)
      |>.defect_multiset_singleton inner
        (by omega) P

end IBRecons

end TCTex
end Submission

/-!
# Total-weight structural recollection of concrete polynomial outer brackets

Structural outer-bracket recollection first removes retained wrappers at one
stratum above the inner packet.  The resulting source still evaluates to the
full outer bracket, whose lower-central depth is the sum of the inner and
outer weights.  Repeated semantic support raising therefore reaches that full
total weight using only normalizers strictly above the inner weight.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace SPFactor

/--
A signed-polynomial source whose word weights are all at least `r` evaluates
in the `r`th one-based lower-central layer.
-/
lemma list_series_weight
    {d n r : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    {ι : Type}
    (e : ι → HEFam H)
    (source : List (SPFactor H ι))
    (hsource :
      ∀ factor ∈ source,
        r ≤ factor.word.weight HEAddres.weight) :
    listEval (n := n) e source ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (r - 1) := by
  apply Subgroup.list_prod_mem
  intro value hvalue
  rcases List.mem_map.mp hvalue with ⟨factor, hfactor, rfl⟩
  exact Subgroup.lowerCentralSeries_antitone
    (Nat.sub_le_sub_right (hsource factor hfactor) 1)
    (factor.eval_lower_series e)

end SPFactor

namespace IBWork

/-- The exact worklist value lies at the full outer-bracket lower-central depth. -/
theorem list_series_sub
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (e : ι → HEFam (concreteBasicCommutators.{u} d)) :
    SPFactor.listEval (n := n) e
        (factors packet inner right) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight - 1) := by
  rw [listEval_factors]
  have hindex :
      (inner.word.weight HEAddres.weight - 1) +
            (right.word.weight HEAddres.weight - 1) + 1 =
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight - 1 := by
    have hinnerPos := inner.word_weight_pos
    have hrightPos := right.word_weight_pos
    omega
  simpa only [hindex] using
    element_lower_series
      (SPFactor.list_series_weight
        (n := n) e (basicReductionFactors inner)
          (least_reduction_factors inner))
      (right.eval_lower_series (n := n) e)

/--
Structurally recollect the concrete outer-bracket worklist at the full sum of
the inner and outer weights.  No normalizer at the inner factor's own stratum
is required.
-/
noncomputable def recollection_above_total
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n) :
    SSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) := by
  let initial :=
    source_normalizer_above packet inner right normalizerAbove
      hinnerTruncated
  by_cases htotal :
      inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight ≤ n
  · have htarget :
        (inner.word.weight HEAddres.weight + 1) +
            (right.word.weight HEAddres.weight - 1) =
          inner.word.weight HEAddres.weight +
            right.word.weight HEAddres.weight := by
      have hrightPos := right.word_weight_pos
      omega
    let raised :=
      initial.raiseSupportBy hn (concreteBasicCommutators.{u} d) hH
        (fun strongerWeight _hstrongerWeight =>
          normalizerAbove strongerWeight (by omega))
        (by
          have hinnerPos := inner.word_weight_pos
          omega)
        (right.word.weight HEAddres.weight - 1)
        (by simpa only [htarget] using htotal)
        (fun e => by
          rw [htarget]
          exact
            list_series_sub
              packet inner right e)
    simpa only [htarget] using raised
  · exact
      {
        higherSource := []
        higher_source_truncated := by
          intro factor hfactor
          simp at hfactor
        higher_weight_least := by
          intro factor hfactor
          simp at hfactor
        list_higher_raw := by
          intro e
          simp only [SPFactor.listEval_nil]
          symm
          apply eq_bot_iff.mp
            SCFactor.trunc_last_bot
          exact Subgroup.lowerCentralSeries_antitone (by omega)
            (list_series_sub
              packet inner right e)
      }

end IBWork
end TCTex
end Submission

/-!
# Structural recollection of exact polynomial inner-span branches

The reconstructed inner source contains an atomic Hall packet, its inverse
wrappers, and the original inner factor.  Every entry has exactly the inner
weight, so structural outer-bracket collection removes retained wrappers
without assuming a normalizer at that same stratum.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u

open CEWord

namespace IBRecons

/-- Structurally recollect the exact reconstructed source above inner weight. -/
noncomputable def source_normalizer_above
    {d n : ℕ}
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n) :
    SSRecol
      (n := n)
      (lowerWeight := inner.word.weight HEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) :=
  SBWork.source_recollect_normalizer
    ((packet.supportedWordFactory
      (WBForm.chooseNormalizerFamily
        (concreteBasicCommutators.{u} d))
      (inner.word.weight HEAddres.weight))
        |>.correctionPacketFactory)
    (TSNormala.ofNormalizerAbove
      normalizerAbove)
    right
    (IBWork.correctionPacket
      packet · right)
    (innerReconstructionSource inner)
    (truncated_inner_reconstruction inner hinnerTruncated)
    (fun _x hx => inner_reconstruction_source inner hx)

/-- Recollect the exact reconstructed branch to an admissible support target. -/
noncomputable def recollect_normalizer_above
    {d n targetWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (hinitialTarget :
      inner.word.weight HEAddres.weight + 1 ≤ targetWeight)
    (htargetTotal :
      targetWeight ≤
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight) :
    SSRecol
      (n := n) (lowerWeight := targetWeight)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) := by
  let initial :=
    source_normalizer_above packet inner right normalizerAbove
      hinnerTruncated
  by_cases htargetTruncated : targetWeight ≤ n
  · exact
      initial.raiseSupportTo hn (concreteBasicCommutators.{u} d) hH
        (fun strongerWeight _hstrongerWeight =>
          normalizerAbove strongerWeight (by omega))
        (by
          have hinnerPos := inner.word_weight_pos
          omega)
        hinitialTarget htargetTruncated
        (fun e =>
          Subgroup.lowerCentralSeries_antitone
            (Nat.sub_le_sub_right htargetTotal 1)
            (list_series_sub
              packet inner right e))
  · exact
      {
        higherSource := []
        higher_source_truncated := by
          intro factor hfactor
          simp at hfactor
        higher_weight_least := by
          intro factor hfactor
          simp at hfactor
        list_higher_raw := by
          intro e
          simp only [SPFactor.listEval_nil]
          symm
          apply eq_bot_iff.mp
            SCFactor.trunc_last_bot
          exact Subgroup.lowerCentralSeries_antitone (by omega)
            (list_series_sub
              packet inner right e)
      }

/-- Recollect the exact reconstructed branch at full bracket depth. -/
noncomputable def recollection_above_total
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n) :
    SSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet inner right) :=
  recollect_normalizer_above hn hH packet inner right
    normalizerAbove hinnerTruncated
      (by
        have hrightPos := right.word_weight_pos
        omega)
      (Nat.le_refl _)

/-- Transport reconstructed recollection back to the original correction packet. -/
noncomputable def recollection_normalizer_above
    {d n targetWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n)
    (hinitialTarget :
      inner.word.weight HEAddres.weight + 1 ≤ targetWeight)
    (htargetTotal :
      targetWeight ≤
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight) :
    SSRecol
      (n := n) (lowerWeight := targetWeight)
      (concreteBasicCommutators.{u} d)
      (IBWork.correctionPacket
        packet inner right).factors :=
  (recollect_normalizer_above hn hH packet inner right
    normalizerAbove hinnerTruncated hinitialTarget htargetTotal)
      |>.of_list_eq
        (list_factors_packet packet inner right)

/-- Transport full-depth recollection back to the original correction packet. -/
noncomputable def
    normalizer_above_total
    {d n : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    {ι : Type}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (inner right :
      SPFactor
        (concreteBasicCommutators.{u} d) ι)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight HEAddres.weight < strongerWeight →
          TSNormal
            (n := n) (lowerWeight := strongerWeight)
              (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight HEAddres.weight < n) :
    SSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight HEAddres.weight +
          right.word.weight HEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (IBWork.correctionPacket
        packet inner right).factors :=
  recollection_normalizer_above hn hH packet
    inner right normalizerAbove hinnerTruncated
      (by
        have hrightPos := right.word_weight_pos
        omega)
      (Nat.le_refl _)

end IBRecons
end TCTex
end Submission

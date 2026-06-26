import Towers.Group.HallBasic.AssociatedGradedSpanning
import Towers.Group.Zassenhaus.ReductionFactors
import Towers.Group.Zassenhaus.FormulaChooseSubstitution
import Towers.Group.Zassenhaus.BracketPacketWorklist
import Towers.Group.Zassenhaus.WorklistRecursiveRecollection
import Towers.Group.Zassenhaus.FormulaTotalSupport
import Towers.Group.Zassenhaus.OuterWorklistRecollection
import Towers.Group.Zassenhaus.SourceSupportEndpoint
import Towers.Group.Zassenhaus.SourceRecollectionCongruence
import Towers.Group.Zassenhaus.SourceSupportRaising
import Towers.Group.Zassenhaus.OuterWorklistInventory
import Towers.Group.Zassenhaus.SourceRecollectionNormalization
import Towers.Group.Zassenhaus.SharpCorrectionDescent
import Mathlib.Data.Prod.Lex

-- Merged from PacketHallRankDescent.lean

/-!
# Hall-rank descent for concrete symbolic inner packets

The classical Hall collector repairs a non-admissible left-normed bracket by
first reducing its inner bracket to atomic Hall-basic trees.  Each resulting
outer bracket then has a strictly smaller reverse finite-rank defect.

Concrete symbolic basic reduction already produces the required atomic
packet.  This file records the bridge from packet membership to indexed
Hall-basic trees and transfers the classical rank-defect decrease to those
symbolic factors.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex
namespace HEWord

universe u

/-- A concrete basic-reduction factor expands to its indexed Hall-basic tree. -/
@[simp]
theorem tree_reduction_factor
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
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
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
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
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx : x ∈ basicReductionFactors factor) :
    (tree x.word).IsBasic := by
  rcases indexed_tree_factors factor hx with
    ⟨i, _hx, htree⟩
  rw [htree]
  exact HallTree.indexed_tree i

/-- Every tree in a concrete basic-reduction packet has the inner tree's weight. -/
theorem tree_reduction_factors
    {d inputWeight : ℕ}
    (factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx : x ∈ basicReductionFactors factor) :
    (tree x.word).weight = (tree factor.word).weight := by
  simpa only [tree_weight] using
    word_reduction_factors factor hx

/--
After symbolic inner reduction, bracketing any emitted atom with an unchanged
basic outer tree strictly decreases the classical Hall bracket rank defect.
-/
theorem bracket_defect_factors
    {d inputWeight : ℕ}
    (inner :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
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

end HEWord
end TCTex
end Towers

-- Merged from PacketOuterBracketWorklist.lean

/-!
# Bracketing concrete inner-reduction packets with an outer factor

Explicit Hall reduction replaces an arbitrary concrete symbolic factor by a
finite atomic packet.  To mirror the classical Hall-basis descent, the next
symbolic operation must bracket that inner packet with an unchanged outer
factor before recurring on the resulting outer brackets.

This file constructs the exact finite powered source using the unrestricted
outer-bracket packet worklist.  The Hall-Petresco packet is instantiated at
support bound zero, so it supplies a correction packet for every atomic inner
factor without additional side conditions.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement
open HEWord

namespace CBWorka

/-- A cutoff Hall-Petresco packet supplies an adjacent correction everywhere. -/
noncomputable def correctionPacket
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (left right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    TCPkt n left right :=
  ((packet.powerSupportedFactory
      hinputWeight 0).correctionPacketFactory).packet
    left right (Nat.zero_le _) (Nat.zero_le _)

/--
Exact powered source for the bracket of one concrete inner-reduction packet
with an unchanged outer-right factor.
-/
noncomputable def factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  PBWork.factors right
    (correctionPacket packet hinputWeight · right)
    (basicReductionFactors inner)

/--
The concrete inner-packet worklist evaluates exactly to the powered outer
bracket of the atomic Hall-reduction packet and the unchanged right factor.
-/
theorem listEval_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (factors packet hinputWeight inner right) =
      ⁅SPFactora.listEval (n := n) q
          (basicReductionFactors inner),
        right.eval (n := n) q⁆ :=
  PBWork.listEval_factors right
    (correctionPacket packet hinputWeight · right) q
      (basicReductionFactors inner)

/-- The concrete worklist retains the lower support bound of the inner packet. -/
theorem weight_least_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    SPFactora.WordWeightLeast
      (inner.word.weight PEAddres.weight)
      (factors packet hinputWeight inner right) :=
  PBWork.weight_least_factors
    right (correctionPacket packet hinputWeight · right)
      (least_reduction_factors inner)

/-- Truncating the inner factor physically truncates its outer-bracket worklist. -/
theorem isTruncated_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (factors packet hinputWeight inner right) :=
  PBWork.isTruncated_factors right
    (correctionPacket packet hinputWeight · right)
      (truncated_reduction_factors inner hinnerTruncated)

end CBWorka
end TCTex
end Towers

-- Merged from PacketOuterBracketReconstructionWorklist.lean

/-!
# Exact reconstruction worklists for powered inner-span branches

Classical associated-graded Hall reduction replaces an inner bracket by its
atomic basic-tree span before bracketing with an unchanged outer factor.  At
the group level, the inner atomic packet differs from the original powered
factor by a semantically higher residual.

Appending that raw residual to the atomic packet reconstructs the original
powered inner factor exactly.  Applying the powered outer-bracket worklist to
the reconstructed source therefore gives an exact nonlinear counterpart of
the classical inner-span branch.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement
open HEWord

namespace BRWork

/--
The atomic Hall packet followed by its raw residual reconstructs one powered
inner factor.
-/
noncomputable def innerReconstructionSource
    {d inputWeight : ℕ}
    (inner :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  basicReductionFactors inner ++ basicRawSource inner

/-- The reconstruction source evaluates exactly to the original inner factor. -/
theorem list_inner_reconstruction
    {d n inputWeight : ℕ}
    (inner :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (innerReconstructionSource inner) =
      inner.eval (n := n) q := by
  rw [innerReconstructionSource, SPFactora.listEval_append,
    reduction_raw_source]
  group

/-- The reconstruction source retains the original inner support bound. -/
theorem least_inner_reconstruction
    {d inputWeight : ℕ}
    (inner :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    SPFactora.WordWeightLeast
      (inner.word.weight PEAddres.weight)
      (innerReconstructionSource inner) := by
  intro factor hfactor
  simp only [innerReconstructionSource, basicRawSource,
    List.mem_append, List.mem_singleton] at hfactor
  rcases hfactor with hfactor | hfactor | rfl
  · exact least_reduction_factors inner factor hfactor
  · rw [SPFactora.inverseList] at hfactor
    rcases List.mem_map.mp hfactor with ⟨sourceFactor, hsourceFactor, rfl⟩
    simpa only [SPFactora.word_neg] using
      least_reduction_factors inner sourceFactor
        (by simpa using hsourceFactor)
  · exact Nat.le_refl _

/-- Every factor in the reconstruction source has exactly the inner weight. -/
theorem inner_reconstruction_source
    {d inputWeight : ℕ}
    (inner :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hfactor : factor ∈ innerReconstructionSource inner) :
    factor.word.weight PEAddres.weight =
      inner.word.weight PEAddres.weight := by
  simp only [innerReconstructionSource, basicRawSource,
    List.mem_append, List.mem_singleton] at hfactor
  rcases hfactor with hfactor | hfactor | rfl
  · exact word_reduction_factors inner hfactor
  · rw [SPFactora.inverseList] at hfactor
    rcases List.mem_map.mp hfactor with ⟨sourceFactor, hsourceFactor, rfl⟩
    simpa only [SPFactora.word_neg] using
      word_reduction_factors inner
        (by simpa using hsourceFactor)
  · rfl

/-- Truncating the inner factor truncates its exact reconstruction source. -/
theorem truncated_inner_reconstruction
    {d n inputWeight : ℕ}
    (inner :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (innerReconstructionSource inner) := by
  intro factor hfactor
  rcases List.mem_append.mp hfactor with hfactor | hfactor
  · exact truncated_reduction_factors inner hinnerTruncated factor hfactor
  · exact
      truncated_reduction_source inner hinnerTruncated
        factor hfactor

/--
Exact powered outer-bracket worklist for the reconstructed inner source and
one unchanged outer-right factor.
-/
noncomputable def factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  PBWork.factors right
    (CBWorka.correctionPacket
      packet hinputWeight · right)
    (innerReconstructionSource inner)

/--
The reconstruction worklist evaluates exactly to the full powered outer
commutator with the original inner factor.
-/
theorem listEval_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (factors packet hinputWeight inner right) =
      ⁅inner.eval (n := n) q, right.eval (n := n) q⁆ := by
  rw [factors,
    PBWork.listEval_factors,
    list_inner_reconstruction]

/--
The reconstruction worklist and the original Hall-Petresco correction packet
are pointwise evaluation-equivalent symbolic sources.
-/
theorem list_factors_packet
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (factors packet hinputWeight inner right) =
      SPFactora.listEval q
        (CBWorka.correctionPacket
          packet hinputWeight inner right).factors := by
  rw [listEval_factors,
    (CBWorka.correctionPacket
      packet hinputWeight inner right).listEval_eq]

/-- The reconstruction worklist retains the original inner support bound. -/
theorem weight_least_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    SPFactora.WordWeightLeast
      (inner.word.weight PEAddres.weight)
      (factors packet hinputWeight inner right) :=
  PBWork.weight_least_factors
    right
    (CBWorka.correctionPacket
      packet hinputWeight · right)
    (least_inner_reconstruction inner)

/-- Truncating the inner factor truncates the reconstruction worklist. -/
theorem isTruncated_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n) :
    SPFactora.IsTruncated n
      (factors packet hinputWeight inner right) :=
  PBWork.isTruncated_factors right
    (CBWorka.correctionPacket
      packet hinputWeight · right)
    (truncated_inner_reconstruction inner hinnerTruncated)

/-- The exact reconstruction worklist lies at the full outer-bracket depth. -/
theorem list_series_sub
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (factors packet hinputWeight inner right) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight - 1) := by
  rw [listEval_factors]
  have hindex :
      (inner.word.weight PEAddres.weight - 1) +
            (right.word.weight PEAddres.weight - 1) + 1 =
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight - 1 := by
    have hinnerPos := inner.word_weight_pos
    have hrightPos := right.word_weight_pos
    omega
  simpa only [hindex] using
    element_lower_series
      (inner.eval_lower_series (n := n) q)
      (right.eval_lower_series (n := n) q)

end BRWork
end TCTex
end Towers

-- Merged from PacketOuterBracketStructuralRecollection.lean

/-!
# Structural recollection of concrete inner-packet outer brackets

The generic outer-bracket worklist collector removes retained conjugating
wrappers by structural recursion.  This file specializes that construction to
the atomic Hall packet emitted by concrete basic reduction.

The specialization assumes normalizers only at weights strictly larger than
the inner factor's weight.  It therefore exposes the non-circular adapter
needed by expanded-Jacobi continuation.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace CBWorka

/--
Structurally recollect the exact concrete outer-bracket worklist using only
normalizers strictly above the inner factor's Hall-weight stratum.
-/
noncomputable def source_normalizer_above
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n) :
    TSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (factors packet hinputWeight inner right) :=
  PBWork.source_recollect_normalizer
    ((packet.powerSupportedFactory
      hinputWeight
      (inner.word.weight PEAddres.weight))
        |>.correctionPacketFactory)
    (SSNormal.ofNormalizerAbove
      normalizerAbove)
    right
    (correctionPacket packet hinputWeight · right)
    (basicReductionFactors inner)
    (truncated_reduction_factors inner hinnerTruncated)
    (fun _x hx => word_reduction_factors inner hx)

end CBWorka
end TCTex
end Towers

-- Merged from PacketOuterBracketTotalWeightSupport.lean

/-!
# Total-weight support for concrete inner-packet outer brackets

Atomic Hall reduction replaces an arbitrary inner word by factors of exactly
the same weight.  Bracketing each atomic factor with one fixed outer-right
factor therefore emits Hall-Petresco corrections supported at the sum of the
original inner and outer weights.

The unrestricted outer-bracket worklist also retains conjugating copies of
the atomic factors.  This file isolates its genuinely descending terminal
correction source from those wrappers.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace CBWorka

/-- Every retained adjacent correction has the sum of its two parent weights. -/
theorem add_packet_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (left right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hfactor :
      factor ∈ (correctionPacket packet hinputWeight left right).factors) :
    left.word.weight PEAddres.weight +
        right.word.weight PEAddres.weight ≤
      factor.word.weight PEAddres.weight := by
  exact
    packet.add_supported_factors
      hinputWeight left right (Nat.zero_le _) (Nat.zero_le _) hfactor

/--
Flatten only the terminal Hall-Petresco corrections in the exact outer
bracket worklist, omitting the retained conjugating copies.
-/
noncomputable def terminalCorrectionFactors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    List
      (SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :=
  (basicReductionFactors inner).flatMap fun left =>
    (correctionPacket packet hinputWeight left right).factors

/-- Terminal corrections are supported at the outer total weight. -/
theorem least_terminal_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    SPFactora.WordWeightLeast
      (inner.word.weight PEAddres.weight +
        right.word.weight PEAddres.weight)
      (terminalCorrectionFactors packet hinputWeight inner right) := by
  intro factor hfactor
  rw [terminalCorrectionFactors] at hfactor
  rcases List.mem_flatMap.mp hfactor with ⟨left, hleft, hfactor⟩
  have hleftWeight :=
    word_reduction_factors inner hleft
  simpa only [hleftWeight] using
    add_packet_factors
      packet hinputWeight left right hfactor

/-- Terminal corrections are physically below the truncation cutoff. -/
theorem truncated_terminal_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight) :
    SPFactora.IsTruncated n
      (terminalCorrectionFactors packet hinputWeight inner right) := by
  intro factor hfactor
  rw [terminalCorrectionFactors] at hfactor
  rcases List.mem_flatMap.mp hfactor with ⟨left, _hleft, hfactor⟩
  exact
    (correctionPacket packet hinputWeight left right).word_weight_cutoff
      factor hfactor

end CBWorka
end TCTex
end Towers

-- Merged from PacketOuterBracketWorklistRecollection.lean

/-!
# Recollecting concrete inner-packet outer-bracket worklists

Concrete Hall reduction replaces an inner bracket by a finite atomic packet.
Bracketing that packet with an unchanged outer factor gives an exact powered
worklist.  Its value lies one lower-central layer above the inner packet's
physical support bound, so a current-stratum semantic normalizer recollects
the worklist into its strictly higher tail.

This is the concrete bridge between atomic inner reduction and the
measure-decreasing outer-bracket recursion used by Hall collection.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace CBWorka

/--
The concrete inner-packet outer-bracket worklist evaluates one lower-central
layer above the common weight of the atomic inner packet.
-/
theorem list_factors_series
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (factors packet hinputWeight inner right) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (inner.word.weight PEAddres.weight) :=
  PBWork.list_factors_series
    right
      (correctionPacket packet hinputWeight · right)
      (basicReductionFactors inner)
      (least_reduction_factors inner) q

/--
Normalize the concrete inner-packet outer-bracket worklist and retain its
strictly higher coordinate tail.
-/
noncomputable def source_recollection_normalizer
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizer :
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight :=
            inner.word.weight PEAddres.weight)
          (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n) :
    TSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (factors packet hinputWeight inner right) :=
  PBWork.source_recollection_normalizer
    hn (concreteBasicCommutators.{u} d) hH normalizer right
      (correctionPacket packet hinputWeight · right)
      (basicReductionFactors inner) inner.word_weight_pos hinnerTruncated
      (truncated_reduction_factors inner hinnerTruncated)
      (least_reduction_factors inner)

/-- Use a normalizer family at the inner factor's common support bound. -/
noncomputable def recollection_normalizer_family
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight)
          (concreteBasicCommutators.{u} d))
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n) :
    TSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (factors packet hinputWeight inner right) :=
  source_recollection_normalizer hn hH packet hinputWeight inner right
    (family.normalizer
      (inner.word.weight PEAddres.weight))
    hinnerTruncated

end CBWorka
end TCTex
end Towers

-- Merged from PacketOuterBracketReconstructionStructuralRecollection.lean

/-!
# Structural recollection of exact powered inner-span branches

The reconstructed inner source contains an atomic Hall packet, its inverse
wrappers, and the original inner factor.  Every entry still has exactly the
inner weight.  The structural outer-bracket collector can therefore remove
its retained wrappers without assuming a normalizer at that same stratum.

The resulting exact full powered commutator can then be raised to any support
target up to the sum of the inner and outer weights.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace BRWork

/--
Structurally recollect the exact reconstructed outer-bracket source one layer
above the inner weight.
-/
noncomputable def source_normalizer_above
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n) :
    TSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight PEAddres.weight + 1)
      (concreteBasicCommutators.{u} d)
      (factors packet hinputWeight inner right) :=
  PBWork.source_recollect_normalizer
    ((packet.powerSupportedFactory
      hinputWeight
      (inner.word.weight PEAddres.weight))
        |>.correctionPacketFactory)
    (SSNormal.ofNormalizerAbove
      normalizerAbove)
    right
    (CBWorka.correctionPacket
      packet hinputWeight · right)
    (innerReconstructionSource inner)
    (truncated_inner_reconstruction inner hinnerTruncated)
    (fun _x hx => inner_reconstruction_source inner hx)

/--
Structurally recollect the exact full powered outer commutator to any support
target bounded by its full lower-central depth.
-/
noncomputable def recollect_normalizer_above
    {d n inputWeight targetWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (hinitialTarget :
      inner.word.weight PEAddres.weight + 1 ≤ targetWeight)
    (htargetTotal :
      targetWeight ≤
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight) :
    TSRecol
      (n := n) (lowerWeight := targetWeight)
      (concreteBasicCommutators.{u} d)
      (factors packet hinputWeight inner right) := by
  let initial :=
    source_normalizer_above packet hinputWeight inner right
      normalizerAbove hinnerTruncated
  by_cases htargetTruncated : targetWeight ≤ n
  · exact
      initial.raiseSupportTo hn (concreteBasicCommutators.{u} d) hH
        (fun strongerWeight _hstrongerWeight =>
          normalizerAbove strongerWeight (by omega))
        (by
          have hinnerPos := inner.word_weight_pos
          omega)
        hinitialTarget htargetTruncated
        (fun q =>
          Subgroup.lowerCentralSeries_antitone
            (Nat.sub_le_sub_right htargetTotal 1)
            (list_series_sub
              packet hinputWeight inner right q))
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
          intro q
          simp only [SPFactora.listEval_nil]
          symm
          apply eq_bot_iff.mp
            SPFactora.trunc_last_bot
          exact Subgroup.lowerCentralSeries_antitone (by omega)
            (list_series_sub
              packet hinputWeight inner right q)
      }

/--
Structurally recollect the exact full powered outer commutator at its total
inner-plus-outer weight.
-/
noncomputable def recollection_above_total
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n) :
    TSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet hinputWeight inner right) :=
  recollect_normalizer_above hn hH packet hinputWeight
    inner right normalizerAbove hinnerTruncated
      (by
        have hrightPos := right.word_weight_pos
        omega)
      (Nat.le_refl _)

/--
Replace the original Hall-Petresco correction packet by the exact
reconstruction branch and recollect it at any admissible support target.
-/
noncomputable def recollection_normalizer_above
    {d n inputWeight targetWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (hinitialTarget :
      inner.word.weight PEAddres.weight + 1 ≤ targetWeight)
    (htargetTotal :
      targetWeight ≤
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight) :
    TSRecol
      (n := n) (lowerWeight := targetWeight)
      (concreteBasicCommutators.{u} d)
      (CBWorka.correctionPacket
        packet hinputWeight inner right).factors :=
  (recollect_normalizer_above hn hH packet hinputWeight
    inner right normalizerAbove hinnerTruncated hinitialTarget htargetTotal)
      |>.of_list_eq
        (list_factors_packet
          packet hinputWeight inner right)

/--
Replace the original Hall-Petresco correction packet by the exact
reconstruction branch and recollect it at full outer-bracket depth.
-/
noncomputable def
    normalizer_above_total
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n) :
    TSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (CBWorka.correctionPacket
        packet hinputWeight inner right).factors :=
  recollection_normalizer_above hn hH packet
    hinputWeight inner right normalizerAbove hinnerTruncated
      (by
        have hrightPos := right.word_weight_pos
        omega)
      (Nat.le_refl _)

end BRWork
end TCTex
end Towers

-- Merged from PacketOuterBracketTotalStructuralRecollection.lean

/-!
# Total-weight structural recollection of concrete outer brackets

Structural outer-bracket recollection first removes retained wrappers at one
stratum above the inner packet.  The resulting source still evaluates to the
full outer bracket, whose lower-central depth is the sum of the inner and
outer weights.  Repeated semantic support raising therefore reaches that full
total weight using only normalizers strictly above the inner weight.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace CBWorka

/-- The exact worklist value lies at the full outer-bracket lower-central depth. -/
theorem list_series_sub
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (q : ℕ) :
    SPFactora.listEval (n := n) q
        (factors packet hinputWeight inner right) ∈
      Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight - 1) := by
  rw [listEval_factors]
  have hindex :
      (inner.word.weight PEAddres.weight - 1) +
            (right.word.weight PEAddres.weight - 1) + 1 =
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight - 1 := by
    have hinnerPos := inner.word_weight_pos
    have hrightPos := right.word_weight_pos
    omega
  simpa only [hindex] using
    element_lower_series
      (SPFactora.list_series_weight
        (n := n) q (basicReductionFactors inner)
          (least_reduction_factors inner))
      (right.eval_lower_series (n := n) q)

/--
Structurally recollect the concrete outer-bracket worklist at the full sum of
the inner and outer weights.  No normalizer at the inner factor's own stratum
is required.
-/
noncomputable def recollection_above_total
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n) :
    TSRecol
      (n := n)
      (lowerWeight :=
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight)
      (concreteBasicCommutators.{u} d)
      (factors packet hinputWeight inner right) := by
  let initial :=
    source_normalizer_above packet hinputWeight inner right
      normalizerAbove hinnerTruncated
  by_cases htotal :
      inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight ≤ n
  · have htarget :
        (inner.word.weight PEAddres.weight + 1) +
            (right.word.weight PEAddres.weight - 1) =
          inner.word.weight PEAddres.weight +
            right.word.weight PEAddres.weight := by
      have hrightPos := right.word_weight_pos
      omega
    let raised :=
      initial.raiseSupportBy hn (concreteBasicCommutators.{u} d) hH
        (fun strongerWeight _hstrongerWeight =>
          normalizerAbove strongerWeight (by omega))
        (by
          have hinnerPos := inner.word_weight_pos
          omega)
        (right.word.weight PEAddres.weight - 1)
        (by simpa only [htarget] using htotal)
        (fun q => by
          rw [htarget]
          exact
            list_series_sub
              packet hinputWeight inner right q)
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
          intro q
          simp only [SPFactora.listEval_nil]
          symm
          apply eq_bot_iff.mp
            SPFactora.trunc_last_bot
          exact Subgroup.lowerCentralSeries_antitone (by omega)
            (list_series_sub
              packet hinputWeight inner right q)
      }

end CBWorka
end TCTex
end Towers

-- Merged from PacketOuterBracketRecursionInventory.lean

/-!
# Recursive inventory of concrete inner-packet outer brackets

The exact outer-bracket worklist retains same-stratum wrappers around its
recursive tail, while every terminal Hall-Petresco correction is supported
strictly above either parent.  This file packages that split for the concrete
atomic inner-reduction packet.

This is the finite source-level interface needed to combine outer Hall-rank
recursion for atomic brackets with ordinary weight recursion for correction
terms.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace CBWorka

/-- Every concrete worklist factor is a wrapper or a terminal correction. -/
theorem or_terminal_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx : x ∈ factors packet hinputWeight inner right) :
    (∃ left ∈ basicReductionFactors inner, x = left) ∨
      (∃ left ∈ basicReductionFactors inner, x = left.neg) ∨
        x ∈ terminalCorrectionFactors packet hinputWeight inner right := by
  rcases
      PBWork.left_or_factors
        right
          (correctionPacket packet hinputWeight · right) hx with
    hleft | hleft | hcorrection
  · exact Or.inl hleft
  · exact Or.inr (Or.inl hleft)
  · rcases hcorrection with ⟨left, hleft, hfactor⟩
    exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨left, hleft, hfactor⟩))

/-- Terminal corrections have weight strictly above the inner packet. -/
theorem inner_terminal_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hfactor :
      factor ∈
        terminalCorrectionFactors packet hinputWeight inner right) :
    inner.word.weight PEAddres.weight <
      factor.word.weight PEAddres.weight := by
  have htotal :=
    least_terminal_factors
      packet hinputWeight inner right factor hfactor
  have hrightPos := right.word_weight_pos
  omega

/-- Terminal corrections have weight strictly above the outer-right factor. -/
theorem right_terminal_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {factor :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hfactor :
      factor ∈
        terminalCorrectionFactors packet hinputWeight inner right) :
    right.word.weight PEAddres.weight <
      factor.word.weight PEAddres.weight := by
  have htotal :=
    least_terminal_factors
      packet hinputWeight inner right factor hfactor
  have hinnerPos := inner.word_weight_pos
  omega

/--
Every concrete worklist factor is an atomic wrapper or is strictly heavier
than the original inner packet.
-/
theorem or_neg_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx : x ∈ factors packet hinputWeight inner right) :
    (∃ left ∈ basicReductionFactors inner, x = left ∨ x = left.neg) ∨
      inner.word.weight PEAddres.weight <
        x.word.weight PEAddres.weight := by
  rcases
      or_terminal_factors
        packet hinputWeight inner right hx with
    hleft | hleft | hcorrection
  · rcases hleft with ⟨left, hleft, hxleft⟩
    exact Or.inl ⟨left, hleft, Or.inl hxleft⟩
  · rcases hleft with ⟨left, hleft, hxleft⟩
    exact Or.inl ⟨left, hleft, Or.inr hxleft⟩
  · exact
      Or.inr
        (inner_terminal_factors
          packet hinputWeight inner right hcorrection)

end CBWorka
end TCTex
end Towers

-- Merged from PacketOuterBracketCorrectionNormalization.lean

/-!
# Deep normalization of concrete powered outer-bracket correction packets

The exact reconstruction worklist recollects a concrete Hall-Petresco
correction packet to the full inner-plus-outer bracket depth using only
normalizers strictly above the inner factor's weight.  Normalizing at that
endpoint produces a correction coordinate block with the same full support.

Weakening the endpoint back to the inner parent support preserves its
coordinate block, so the existing sharp cutoff-defect descent theorem applies
without requiring a normalizer at the inner factor's own stratum.

The file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord
open TSNorma

namespace BRWork

/--
Normalize the reconstructed correction packet at any admissible outer-bracket
support target.
-/
noncomputable def correction_normalization_normalizer
    {d n inputWeight targetWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (hinitialTarget :
      inner.word.weight PEAddres.weight + 1 ≤ targetWeight)
    (htargetTotal :
      targetWeight ≤
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight) :
    TSNorma
      (targetWeight - 1)
      (CBWorka.correctionPacket
        packet hinputWeight inner right) :=
  (CBWorka.correctionPacket
    packet hinputWeight inner right)
      |>.normalization_recollection_support
        (recollection_normalizer_above
          hn hH packet hinputWeight inner right normalizerAbove
            hinnerTruncated hinitialTarget htargetTotal)
        (normalizerAbove targetWeight (by omega))
        (by
          have hinnerPos := inner.word_weight_pos
          omega)

/--
Normalize the reconstructed correction packet at its full inner-plus-outer
bracket depth.
-/
noncomputable def
    normalization_normalizer_above
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n) :
    TSNorma
      (inner.word.weight PEAddres.weight +
        right.word.weight PEAddres.weight - 1)
      (CBWorka.correctionPacket
        packet hinputWeight inner right) :=
  correction_normalization_normalizer hn hH packet
    hinputWeight inner right normalizerAbove hinnerTruncated
      (by
        have hrightPos := right.word_weight_pos
        omega)
      (Nat.le_refl _)

/--
Expose the full-depth correction endpoint sharply above the inner parent.
-/
noncomputable def
    sharp_above_total
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n) :
    TSNorma
      (inner.word.weight PEAddres.weight)
      (CBWorka.correctionPacket
        packet hinputWeight inner right) :=
  (normalization_normalizer_above hn hH packet
    hinputWeight inner right normalizerAbove hinnerTruncated).weaken (by
      have hrightPos := right.word_weight_pos
      omega)

/--
The sharply exposed full-depth correction endpoint strictly decreases the
cutoff-defect multiset when it replaces the inner parent.
-/
lemma
    normalization_total_multiset
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (P :
      List
        (SPFactora
          (concreteBasicCommutators.{u} d) inputWeight)) :
    SPFactora.CutoffDefectMultiset n
      (P ++
        (sharp_above_total
          hn hH packet hinputWeight inner right normalizerAbove
            hinnerTruncated).coordinates.factors (n := n))
      (P ++ [inner]) :=
  multisetAppendSingleton
    (sharp_above_total
      hn hH packet hinputWeight inner right normalizerAbove hinnerTruncated)
    P

end BRWork
end TCTex
end Towers

-- Merged from PacketOuterBracketTargetStructuralRecollection.lean

/-!
# Target-weight structural recollection of concrete outer brackets

The concrete inner-packet outer-bracket worklist can be raised to any support
target between the first structurally available stratum and its full
lower-central depth.  This exposes the exact endpoint needed by callers while
retaining the non-circular requirement that normalizers are supplied only
strictly above the inner factor's weight.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace CBWorka

/--
Structurally recollect a concrete outer-bracket worklist to any support target
bounded by its full bracket weight.
-/
noncomputable def recollect_normalizer_above
    {d n inputWeight targetWeight : ℕ}
    (hn : 2 ≤ n)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (concreteCommutatorsWeight.{u} d s).FormsAssocGradedbasis
              (n := n))
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    (normalizerAbove :
      ∀ strongerWeight : ℕ,
        inner.word.weight PEAddres.weight < strongerWeight →
          TSNormalb
            (n := n) (inputWeight := inputWeight)
              (lowerWeight := strongerWeight)
                (concreteBasicCommutators.{u} d))
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (hinitialTarget :
      inner.word.weight PEAddres.weight + 1 ≤ targetWeight)
    (htargetTotal :
      targetWeight ≤
        inner.word.weight PEAddres.weight +
          right.word.weight PEAddres.weight) :
    TSRecol
      (n := n) (lowerWeight := targetWeight)
      (concreteBasicCommutators.{u} d)
      (factors packet hinputWeight inner right) := by
  let initial :=
    source_normalizer_above packet hinputWeight inner right
      normalizerAbove hinnerTruncated
  by_cases htargetTruncated : targetWeight ≤ n
  · exact
      initial.raiseSupportTo hn (concreteBasicCommutators.{u} d) hH
        (fun strongerWeight _hstrongerWeight =>
          normalizerAbove strongerWeight (by omega))
        (by
          have hinnerPos := inner.word_weight_pos
          omega)
        hinitialTarget htargetTruncated
        (fun q =>
          Subgroup.lowerCentralSeries_antitone
            (Nat.sub_le_sub_right htargetTotal 1)
            (list_series_sub
              packet hinputWeight inner right q))
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
          intro q
          simp only [SPFactora.listEval_nil]
          symm
          apply eq_bot_iff.mp
            SPFactora.trunc_last_bot
          exact Subgroup.lowerCentralSeries_antitone (by omega)
            (list_series_sub
              packet hinputWeight inner right q)
      }

end CBWorka
end TCTex
end Towers

-- Merged from PacketOuterBracketRankedInventory.lean

/-!
# Ranked recursive inventory of concrete inner-packet outer brackets

The exact inner-packet outer-bracket worklist has a lexicographic recursive
shape.  Its terminal Hall-Petresco corrections increase ordinary word weight.
Its same-weight wrappers come from atomic Hall reduction, and bracketing those
atoms with the unchanged outer tree strictly decreases the fixed-weight Hall
rank defect.

This file combines the two progress arguments into one source-level theorem.
It is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HEWord

namespace CBWorka

/--
Every exact worklist factor either comes from a same-weight atomic wrapper
whose outer bracket has smaller Hall-rank defect, or increases ordinary word
weight.
-/
theorem ranked_or_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx : x ∈ factors packet hinputWeight inner right)
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
      inner.word.weight PEAddres.weight <
        x.word.weight PEAddres.weight := by
  rcases
      or_neg_factors
        packet hinputWeight inner right hx with
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
            simpa only [SPFactora.word_neg] using
              (bracket_defect_factors
                inner hleft added originalRight unchanged originalLeft
                  hinnerTree hRightLeft hRightUnchanged hunchangedBasic)⟩
  · exact Or.inr hhigher

end CBWorka
end TCTex
end Towers

-- Merged from PacketOuterBracketLexicographicDescent.lean

/-!
# Lexicographic descent for concrete inner-packet outer brackets

Unrestricted symbolic Hall collection needs two recursion measures.  A
Hall-Petresco terminal correction strictly increases ordinary word weight,
so its cutoff defect decreases.  An atomic wrapper retains the original
inner weight, but its outer Hall bracket has strictly smaller reverse finite
rank defect.

This file packages the lexicographic product of those measures and proves
that every factor emitted by a concrete inner-packet outer-bracket worklist
descends.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SPFactora

/-- Cutoff defect followed by fixed-weight Hall-bracket rank defect. -/
def hallRankedMeasure
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ)
    (factor : SPFactora H inputWeight)
    (rankDefect : ℕ) :
    ℕ × ℕ :=
  (cutoffDefect n factor, rankDefect)

/-- Lexicographic descent for one symbolic Hall task. -/
def HallRankedDescends
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (n : ℕ)
    (child : SPFactora H inputWeight)
    (childRankDefect : ℕ)
    (parent : SPFactora H inputWeight)
    (parentRankDefect : ℕ) :
    Prop :=
  Prod.Lex (· < ·) (· < ·)
    (hallRankedMeasure n child childRankDefect)
    (hallRankedMeasure n parent parentRankDefect)

/-- Hall-ranked descent is well-founded because both components are natural numbers. -/
lemma descends_well_founded
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r} :
    WellFounded
      (fun child parent :
          SPFactora H inputWeight × ℕ =>
        HallRankedDescends n child.1 child.2 parent.1 parent.2) := by
  unfold HallRankedDescends
  exact
    InvImage.wf
      (fun task : SPFactora H inputWeight × ℕ =>
        hallRankedMeasure n task.1 task.2)
      (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf)

/-- Recursion principle for cutoff-defect/Hall-rank symbolic tasks. -/
theorem ranked_descends_induction
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {motive : SPFactora H inputWeight → ℕ → Prop}
    (step :
      ∀ parent parentRankDefect,
        (∀ child childRankDefect,
          HallRankedDescends n child childRankDefect parent parentRankDefect →
            motive child childRankDefect) →
          motive parent parentRankDefect)
    (factor : SPFactora H inputWeight)
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
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (child parent : SPFactora H inputWeight)
    (childRankDefect parentRankDefect : ℕ)
    (hparentTruncated :
      parent.word.weight PEAddres.weight < n)
    (hweight :
      parent.word.weight PEAddres.weight <
        child.word.weight PEAddres.weight) :
    HallRankedDescends n child childRankDefect parent parentRankDefect := by
  apply Prod.Lex.left
  simp only [cutoffDefect]
  omega

/-- At fixed ordinary weight, strict Hall-rank progress decreases the second component. -/
lemma ranked_descends_defect
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (child parent : SPFactora H inputWeight)
    (childRankDefect parentRankDefect : ℕ)
    (hweight :
      child.word.weight PEAddres.weight =
        parent.word.weight PEAddres.weight)
    (hrank : childRankDefect < parentRankDefect) :
    HallRankedDescends n child childRankDefect parent parentRankDefect := by
  simpa only [HallRankedDescends, hallRankedMeasure, cutoffDefect, hweight] using
    (Prod.Lex.right
      (n - parent.word.weight PEAddres.weight) hrank)

end SPFactora

namespace CBWorka

open HEWord

/--
Every factor emitted by one concrete inner-packet outer-bracket worklist
strictly descends in cutoff-defect/Hall-rank lexicographic order.
-/
theorem ranked_descends_factors
    {d n inputWeight : ℕ}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (inner right :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight)
    {x :
      SPFactora
        (concreteBasicCommutators.{u} d) inputWeight}
    (hx : x ∈ factors packet hinputWeight inner right)
    (hinnerTruncated :
      inner.word.weight PEAddres.weight < n)
    (added originalRight unchanged originalLeft :
      HallTree (FreeGenerator.{u} d))
    (hinnerTree :
      tree inner.word = .commutator added originalRight)
    (hRightLeft : originalRight < originalLeft)
    (hRightUnchanged : originalRight < unchanged)
    (hunchangedBasic : unchanged.IsBasic) :
    SPFactora.HallRankedDescends n x
      (HallTree.bracketRankDefect
        ((tree inner.word).weight + unchanged.weight)
        (tree x.word) unchanged)
      inner
      (HallTree.bracketRankDefect
        ((tree inner.word).weight + unchanged.weight)
        originalLeft originalRight) := by
  rcases
      ranked_or_factors
        packet hinputWeight inner right hx added originalRight unchanged
          originalLeft hinnerTree hRightLeft hRightUnchanged hunchangedBasic with
    hwrapped | hhigher
  · rcases hwrapped with ⟨left, hleft, hxleft, hrank⟩
    have hleftWeight :=
      word_reduction_factors inner hleft
    apply
      SPFactora.ranked_descends_defect
    · rcases hxleft with hxleft | hxleft
      · simpa only [hxleft] using hleftWeight
      · simpa only [hxleft, SPFactora.word_neg] using hleftWeight
    · exact hrank
  · exact
      SPFactora.ranked_descends_weight
        x inner _ _ hinnerTruncated hhigher

end CBWorka
end TCTex
end Towers

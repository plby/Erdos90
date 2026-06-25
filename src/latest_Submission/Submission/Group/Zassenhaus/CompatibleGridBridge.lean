import Submission.Group.Zassenhaus.CompatibleListBoundary
import Submission.Group.Zassenhaus.EndpointShapeInterpolation

/-!
# Claim 5 from shape-erased compatible-grid branch lists

Support-compatible correction-grid batches preserve the operational
collector's overlap subtraction.  Once their erased flattened trace is a
permutation of the selected correction-shape trace, the batch profiles
compile to endpoint interpolation and hence to the Claim 5 coordinate
polynomials.

This file states that downstream constructor directly.  It also restates the
remaining all-integral lift as the corresponding truncated signed
recollection law.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Submission
namespace TCTex

universe u


open scoped commutatorElement

open
  EBList
open
  CRLayer
open
  FPInterp
open
  CFSubsti
open
  FIProf

namespace
  EBList
namespace
  PCDecompb

/--
The remaining signed extension after compatible-grid erased-shape batch
profiles have been compiled to endpoint interpolation.
-/
abbrev AILift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      PCDecompb
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    Prop :=
  EFInterp.AILift.{u}
    (d := d)
    (decomposition.fiberProfileInterpolation raw)

/--
The truncated signed recollection law for the packets compiled from
compatible-grid erased-shape batches.
-/
def SatisfiesTruncEval
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      PCDecompb
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    Prop :=
  ∀ (left right :
      LowerCentralTruncation.{u} (FreeGroup (FreeGenerator.{u} d)) n)
    (leftExponent rightExponent : ℤ),
      ((EFInterp.truncNaturalPacket.{u}
        (d := d)
        (decomposition.fiberProfileInterpolation
          raw)).packets.map fun packet =>
            packet.word.eval (HPAtom.eval left right) ^
              packet.profiles.value leftExponent rightExponent).prod =
        ⁅left ^ leftExponent, right ^ rightExponent⁆

/--
The truncated signed recollection law supplies the all-integral lift.
-/
def allLiftSatisfies
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      PCDecompb
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (hlistEval :
      PCDecompb.SatisfiesTruncEval.{u}
        (d := d) decomposition raw) :
    PCDecompb.AILift.{u}
      (d := d) decomposition raw where
  listEval_eq :=
    hlistEval

/--
The all-integral lift recovers the truncated signed recollection law.
-/
lemma satisfies_trunc_all
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      PCDecompb
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (lift :
      PCDecompb.AILift.{u}
        (d := d) decomposition raw) :
    PCDecompb.SatisfiesTruncEval.{u}
      (d := d) decomposition raw :=
  lift.listEval_eq

/--
For compatible-grid erased-shape batches, the remaining signed extension is
exactly the truncated signed recollection law.
-/
theorem satisfies_trunc_lift
    {d n : ℕ}
    {layer : NRLayer n 1 1}
    (decomposition :
      PCDecompb
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp)) :
    PCDecompb.SatisfiesTruncEval.{u}
        (d := d) decomposition raw ↔
      PCDecompb.AILift.{u}
        (d := d) decomposition raw :=
  ⟨decomposition.allLiftSatisfies raw,
    decomposition.satisfies_trunc_all raw⟩

end
  PCDecompb
end
  EBList

namespace TSInput

/--
Compatible-grid erased-shape batches, their signed lift, singleton
recollections, and graded Hall bases construct the Claim 5 coordinate
polynomials.
-/
theorem
    gridBranchesLift
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (decomposition :
      PCDecompb
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (lift :
      PCDecompb.AILift.{u}
        (d := d) decomposition raw)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.fiberInterpolationLift
    hn H hH
      (decomposition.fiberProfileInterpolation raw)
      lift hsourceSupported factorNormalization hinputWeight

/--
The direct truncated signed recollection law is an equivalent constructor
input for the Claim 5 coordinate polynomials.
-/
theorem
    coordGridTrunc
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    {layer : NRLayer n 1 1}
    (decomposition :
      PCDecompb
        layer (by simp) (by simp))
    (raw :
      RFProf
        n 1 1 (by simp) (by simp))
    (hlistEval :
      PCDecompb.SatisfiesTruncEval.{u}
        (d := d) decomposition raw)
    {e : HEFam H}
    (input :
      TSInput
        (n := n) (inputWeight := inputWeight) H e)
    (hsourceSupported :
      SPFactora.WordWeightLeast inputWeight input.source)
    (factorNormalization :
      ∀ lowerWeight : ℕ,
        ¬n ≤ 2 * lowerWeight →
          TSNormalb
              (n := n) (inputWeight := inputWeight)
                (lowerWeight := lowerWeight + 1) H →
            ∀ (factor : SPFactora H inputWeight),
              factor.word.weight PEAddres.weight = lowerWeight →
              factor.word.weight PEAddres.weight < n →
            TANorm
              (n := n) (lowerWeight := lowerWeight) H factor)
    (hinputWeight : 1 ≤ inputWeight) :
    CollectedPolynomialData (n := n) H e inputWeight :=
  input.gridBranchesLift
    hn H hH decomposition raw
      (decomposition.allLiftSatisfies raw hlistEval)
        hsourceSupported factorNormalization hinputWeight

end TSInput

end TCTex
end Submission

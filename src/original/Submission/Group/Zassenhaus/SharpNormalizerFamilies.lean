import Submission.Group.Zassenhaus.SharpCorrectionNormalization
import Submission.Group.Zassenhaus.UniversalCollectionReduction

/-!
# Families of sharp symbolic Hall-power semantic normalizers

Recursive higher-tail routing must normalize a correction packet above the
actual parent crossed by an insertion, rather than only above the ambient
active stratum.  This file packages normalizers at every support bound into a
single family and derives such a family from the universal semantic builder.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

/-- A semantic coordinate normalizer available at every lower support bound. -/
structure SSNormala
    {d n inputWeight : ℕ}
    (H : ∀ s : ℕ, BCWta.{u} d s) where
  normalizer :
    ∀ lowerWeight : ℕ,
      TSNormalb
        (n := n) (inputWeight := inputWeight)
          (lowerWeight := lowerWeight) H

namespace SSNormala

/-- Choose the correction endpoint normalized sharply above its left parent. -/
noncomputable def normalization_left_weight
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A) :
    TSNorma
      (B.word.weight PEAddres.weight) C :=
  C.normalization_left_weight
    (family.normalizer
      (B.word.weight PEAddres.weight + 1))

/-- Choose the correction endpoint normalized sharply above its right parent. -/
noncomputable def semantic_normalization_word
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A) :
    TSNorma
      (A.word.weight PEAddres.weight) C :=
  C.semantic_normalization_word
    (family.normalizer
      (A.word.weight PEAddres.weight + 1))

/--
Choose a left-parent-sharp endpoint and expose it through a weaker ambient
support stratum.
-/
noncomputable def semantic_left_sharp
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hB : lowerWeight ≤ B.word.weight PEAddres.weight) :
    TSNorma
      lowerWeight C :=
  (family.normalization_left_weight C).weaken hB

/--
Choose a right-parent-sharp endpoint and expose it through a weaker ambient
support stratum.
-/
noncomputable def normalization_right_sharp
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (family :
      SSNormala
        (n := n) (inputWeight := inputWeight) H)
    {B A : SPFactora H inputWeight}
    (C : TCPkt n B A)
    (hA : lowerWeight ≤ A.word.weight PEAddres.weight) :
    TSNorma
      lowerWeight C :=
  (family.semantic_normalization_word C).weaken hA

end SSNormala

namespace TDBuildb

/--
A universal semantic collection builder supplies sharp normalizers at every
support stratum by filtration recursion.
-/
noncomputable def supportedSemanticFamily
    {d n inputWeight : ℕ}
    (hn : 2 ≤ n)
    (H : ∀ s : ℕ, BCWta.{u} d s)
    (hH :
      ∀ s : ℕ,
        1 ≤ s →
          s < n →
            (H s).FormsAssocGradedbasis (n := n))
    (builder :
      TDBuildb
        (n := n) (inputWeight := inputWeight) H) :
    SSNormala
      (n := n) (inputWeight := inputWeight) H where
  normalizer lowerWeight :=
    builder.semanticCoordinateNormalizer hn H hH lowerWeight

end TDBuildb

end TCTex
end Submission

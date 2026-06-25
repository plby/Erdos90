import Towers.Group.Zassenhaus.TransientPacketClassification
import Towers.Group.Zassenhaus.BasicTermSemantics
import Towers.Group.Zassenhaus.ResidualPrincipalInventory

/-!
# Classification of the principal transient rewording term

The principal `basic` recipe rebuilt during transient rewording has the same
physical word, arithmetic weight, and exponent polynomial as its outer
parent.  Consequently it attaches exactly when the parent arithmetic bound
fits the parent word.  In the active case it remains a frontier with the same
cutoff defect as the parent.

This records why termwise outer-root recursion is not a progress argument for
the principal term: its singleton frontier is not strictly smaller than the
outer singleton.  A collector must cancel it contextually while routing the
strict tails and their conjugation corrections.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

namespace SOTerm

/-- A retained frontier term contributes its cutoff defect to the recursive
defect multiset. -/
lemma defect_frontier_multiset
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (expansion :
      TWExp H inputWeight) :
    ∀ {terms : List (SOTerm H inputWeight)},
      .frontier expansion ∈ terms →
        n - expansion.word.weight PEAddres.weight ∈
          frontierDefectMultiset n terms
  | [], hterm => by
      simp at hterm
  | .attached _ :: terms, hterm => by
      simp only [List.mem_cons] at hterm
      rcases hterm with hterm | hterm
      · cases hterm
      · exact
          defect_frontier_multiset
            expansion (terms := terms) hterm
  | .frontier nextExpansion :: terms, hterm => by
      simp only [List.mem_cons] at hterm
      rw [frontierMultisetCons, Multiset.mem_add]
      rcases hterm with hterm | hterm
      · cases hterm
        exact Or.inl (by simp)
      · exact Or.inr <|
          defect_frontier_multiset
            expansion (terms := terms) hterm

end SOTerm

namespace PTSubsti

open BRSpec

/-- The principal temporary term attaches whenever its parent arithmetic
bound already fits the parent word. -/
lemma classified_reword_attached
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hweight :
      outerExpansion.exponentWeight ≤
        outerExpansion.word.weight PEAddres.weight) :
    classifiedTransientTerm hinputWeight hallPair
        (outerExpansion.reword innerWord)
        (TWExp.wordUnit rightWord) =
      .attached
        ((rewordedBasicExpansion hinputWeight outerExpansion innerWord
          rightWord).toWordExpansion (by
            simpa only [exponent_reworded_expansion,
              reworded_expansion_outer hinputWeight
                outerExpansion innerWord rightWord hword] using hweight)) := by
  apply classified_attached_exponent

/-- A non-attachable parent retains its principal temporary term as a
frontier. -/
lemma classified_transient_reword
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hweight :
      ¬ outerExpansion.exponentWeight ≤
        outerExpansion.word.weight PEAddres.weight) :
    classifiedTransientTerm hinputWeight hallPair
        (outerExpansion.reword innerWord)
        (TWExp.wordUnit rightWord) =
      .frontier
        (rewordedBasicExpansion hinputWeight outerExpansion innerWord
          rightWord) := by
  apply classified_transient_exponent
  have hbasicWeight :
      ¬ (rewordedBasicExpansion hinputWeight outerExpansion innerWord
          rightWord).exponentWeight ≤
        (rewordedBasicExpansion hinputWeight outerExpansion innerWord
          rightWord).word.weight PEAddres.weight := by
    simpa only [exponent_reworded_expansion,
    reworded_expansion_outer hinputWeight outerExpansion
      innerWord rightWord hword] using hweight
  simpa only [rewordedBasicExpansion] using hbasicWeight

end PTSubsti

namespace PFSubsti.TAPkt

open BRSpec
open PTSubsti
open SOTerm

/-- In the active case, every packet carrying `basic` retains the principal
temporary frontier. -/
lemma transient_classified_reworded
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hprincipal : packet.PBRecipea)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hweight :
      ¬ outerExpansion.exponentWeight ≤
        outerExpansion.word.weight PEAddres.weight) :
    .frontier
        (rewordedBasicExpansion hinputWeight outerExpansion innerWord
          rightWord) ∈
      packet.transientClassifiedTerms hinputWeight
        (outerExpansion.reword innerWord)
        (TWExp.wordUnit rightWord) := by
  rw [transientClassifiedTerms]
  apply List.mem_map.mpr
  exact
    ⟨hallPair, hprincipal.basic_mem,
      classified_transient_reword
        hinputWeight outerExpansion innerWord rightWord hword hweight⟩

/-- The retained principal temporary frontier contributes exactly the parent
cutoff defect. -/
lemma multiset_classified_terms
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hprincipal : packet.PBRecipea)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord)
    (hweight :
      ¬ outerExpansion.exponentWeight ≤
        outerExpansion.word.weight PEAddres.weight) :
    n - outerExpansion.word.weight PEAddres.weight ∈
      SOTerm.frontierDefectMultiset n
        (packet.transientClassifiedTerms hinputWeight
          (outerExpansion.reword innerWord)
          (TWExp.wordUnit rightWord)) := by
  simpa only [
    reworded_expansion_outer hinputWeight outerExpansion
      innerWord rightWord hword] using
    defect_frontier_multiset
        (n := n)
        (rewordedBasicExpansion hinputWeight outerExpansion innerWord
          rightWord)
        (packet.transient_classified_reworded
          hprincipal hinputWeight outerExpansion innerWord rightWord hword
            hweight)

end PFSubsti.TAPkt

namespace SOTerm

open PTSubsti

/-- The principal temporary frontier singleton has exactly the parent
singleton cutoff defect. -/
lemma frontier_multiset_reworded
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    frontierDefectMultiset n
        [.frontier
          (rewordedBasicExpansion hinputWeight outerExpansion innerWord
            rightWord)] =
      frontierDefectMultiset n [.frontier outerExpansion] := by
  simp only [frontierMultisetCons,
    frontier_multiset_nil,
    reworded_expansion_outer hinputWeight outerExpansion
      innerWord rightWord hword]

/-- The principal temporary singleton cannot be discharged as a strict
outer-root restart: it has the same cutoff defect as the parent singleton. -/
lemma multiset_singleton_reworded
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (hword : outerExpansion.word = .commutator innerWord rightWord) :
    ¬ FrontierDefectMultiset n
        [.frontier
          (rewordedBasicExpansion hinputWeight outerExpansion innerWord
            rightWord)]
        [.frontier outerExpansion] := by
  rw [FrontierDefectMultiset,
    frontier_multiset_reworded
      hinputWeight outerExpansion innerWord rightWord hword]
  exact
    (Multiset.wellFounded_isDershowitzMannaLT (α := ℕ)).irrefl.irrefl _

end SOTerm

end TCTex
end Towers

import Towers.Group.Zassenhaus.Transient
import Towers.Group.Zassenhaus.BifurcatedFrontierRouting

/-!
# Automatic routing data for generated transient frontiers

Every Hall-Petresco block recipe has positive left and right Hall-pair
bidegrees.  Consequently its substituted transient output is a genuine
commutator word.  This file turns that structural fact into the bifurcated
frontier-routing data needed by recursive contextual recollection.

The constructors cover both arbitrary classified packets and the temporary
reworded packets emitted while reducing an outer transient commutator.

This file is intentionally not imported by the existing collection proof.
-/

noncomputable section

namespace Towers
namespace TCTex

universe u

open HACoeff

namespace PTSubsti

/--
Every substituted transient recipe output is syntactically a commutator
word.
-/
lemma words_expansion_commutator
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    ∃ innerWord rightWord : CWord (HEAddres H),
      (wordExpansion hinputWeight R B A).word =
        .commutator innerWord rightWord := by
  rcases pair_bidegree_positive R.positive with
    ⟨innerShape, rightShape, hshape⟩
  change R.erasedShape = .commutator innerShape rightShape at hshape
  refine
    ⟨CWord.hallPairBind B.word A.word innerShape,
      CWord.hallPairBind B.word A.word rightShape, ?_⟩
  simp only [word_wordExpansion, boundWord, hshape,
    CWord.hallPairBind, CWord.bind_commutator]

end PTSubsti

namespace PFSubsti.TAPkt

/--
Every retained frontier of an arbitrary classified transient packet is
syntactically a commutator word.
-/
lemma words_transient_frontier
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A expansion :
      TWExp H inputWeight)
    (hexpansion :
      .frontier expansion ∈
        packet.transientClassifiedTerms hinputWeight B A) :
    ∃ innerWord rightWord : CWord (HEAddres H),
      expansion.word = .commutator innerWord rightWord := by
  rcases
      packet.recipe_transient_frontier
        hinputWeight B A expansion hexpansion with
    ⟨R, _, _, rfl⟩
  exact
    PTSubsti.words_expansion_commutator
      hinputWeight R B A

end PFSubsti.TAPkt

namespace
  BRRoute

/--
Build bifurcated routing data automa for one generated transient
recipe output.
-/
noncomputable def of_wordExpansion
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (R : BRecipe)
    (B A : TWExp H inputWeight) :
    BRRoute
      H packet hinputWeight
        (PTSubsti.wordExpansion
          hinputWeight R B A) := by
  let hwords :=
    PTSubsti.words_expansion_commutator
      hinputWeight R B A
  exact
    { innerWord := Classical.choose hwords
      rightWord := Classical.choose (Classical.choose_spec hwords)
      word_eq := Classical.choose_spec (Classical.choose_spec hwords) }

/--
Recover bifurcated routing data automa for every retained frontier of
an arbitrary classified transient packet.
-/
noncomputable def transient_frontier
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (B A expansion :
      TWExp H inputWeight)
    (hexpansion :
      .frontier expansion ∈
        packet.transientClassifiedTerms hinputWeight B A) :
    BRRoute
      H packet hinputWeight expansion := by
  let hwords :=
    packet
      |>.words_transient_frontier
        hinputWeight B A expansion hexpansion
  exact
    { innerWord := Classical.choose hwords
      rightWord := Classical.choose (Classical.choose_spec hwords)
      word_eq := Classical.choose_spec (Classical.choose_spec hwords) }

/--
Recover bifurcated routing data automa for every retained frontier of
a temporary packet emitted by rewording an outer transient commutator.
-/
noncomputable def
    classified_inner_frontier
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet :
      PFSubsti.TAPkt.{u}
        d n)
    (hinputWeight : 0 < inputWeight)
    (outerExpansion :
      TWExp H inputWeight)
    (innerWord rightWord : CWord (HEAddres H))
    (expansion :
      TWExp H inputWeight)
    (hexpansion :
      .frontier expansion ∈
        packet.transientInnerTerms hinputWeight
          outerExpansion innerWord rightWord) :
    BRRoute
      H packet hinputWeight expansion :=
  transient_frontier packet hinputWeight
    (outerExpansion.reword innerWord)
      (TWExp.wordUnit rightWord)
        expansion hexpansion

end
  BRRoute

end TCTex
end Towers

import Submission.Group.Zassenhaus.CompatiblePacketRouting
import Submission.Group.Zassenhaus.FormulaChooseSubstitution

/-!
# Substituting powered factors into signed-profile Hall-Petresco packets

Support-pattern compression naturally produces signed-profile packets rather
than positive `BRecipe` lists.  This file is the powered analogue of the
signed polynomial substitution layer: it normalizes every signed generalized
binomial block into an explicit repeated-block expansion, attaches the result
to its bound Hall word, and compiles cutoff or universal signed packets into
the correction factory consumed by symbolic Hall-power collection.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

open HACoeff
open CSAggreg
open CEComp
open CFSubsti
open CFExp

namespace BCExp

/--
Normalize one generalized binomial coefficient of a signed symbolic power
exponent.
-/
noncomputable def signedChooseExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (sign : Sign)
    (degree : ℕ) :
    BCExp inputWeight
      (degree * factor.word.weight PEAddres.weight) :=
  BCExp.ringChoose inputWeight
    (factor.word.weight PEAddres.weight)
    degree hinputWeight
      (fun q : ℕ => sign.intValue * factor.exponent q)

@[simp]
lemma signed_choose_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (sign : Sign)
    (degree : ℕ) :
    (signedChooseExpansion
      hinputWeight factor sign degree).eval =
        fun q : ℕ => Ring.choose (sign.intValue * factor.exponent q) degree := by
  apply BCExp.eval_ringChoose hinputWeight
  simpa only [Pi.smul_apply, smul_eq_mul] using
    (factor.exponent_valued_most hinputWeight).smul
      sign.intValue

/--
Normalize a nonempty list of positive-degree signed blocks sharing one parent
factor.
-/
noncomputable def positiveExponentExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight) :
    ∀ (blocks : List Block),
      blocks ≠ [] →
        (∀ block ∈ blocks, 0 < block.degree) →
          BCExp inputWeight
            (degreeSum blocks *
              factor.word.weight PEAddres.weight)
  | [], hnonempty, _ =>
      False.elim (hnonempty rfl)
  | [block], _, _ =>
      signedChooseExpansion hinputWeight factor
        block.sign block.degree
  | block :: nextBlock :: blocks, _, hpositive =>
      reweight (by simp [degreeSum, Nat.add_mul])
        ((signedChooseExpansion hinputWeight factor
          block.sign block.degree).mul
            (positiveExponentExpansion hinputWeight factor
              (nextBlock :: blocks) (by simp)
              (fun next hnext => hpositive next (by simp [hnext]))))
termination_by blocks => blocks.length

@[simp]
lemma positive_exponent_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight) :
    ∀ (blocks : List Block)
      (hnonempty : blocks ≠ [])
      (hpositive : ∀ block ∈ blocks, 0 < block.degree),
      (positiveExponentExpansion
        hinputWeight factor blocks hnonempty hpositive).eval =
          fun q : ℕ => signedBlockProduct (factor.exponent q) blocks
  | [], hnonempty, _ =>
      False.elim (hnonempty rfl)
  | [block], _, _ => by
      simpa only [positiveExponentExpansion,
        signedBlockProduct, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, mul_one] using
          signed_choose_expansion
            hinputWeight factor block.sign block.degree
  | block :: nextBlock :: blocks, _, hpositive => by
      funext q
      rw [positiveExponentExpansion, eval_reweight,
        BCExp.eval_mul,
        signed_choose_expansion,
        positive_exponent_expansion hinputWeight factor
          (nextBlock :: blocks) (by simp)
          (fun next hnext => hpositive next (by simp [hnext]))]
      rfl
termination_by blocks => blocks.length

/-- Normalize any signed block list whose total degree is positive. -/
noncomputable def signedExponentExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (blocks : List Block)
    (hdegree : 0 < degreeSum blocks) :
    BCExp inputWeight
      (degreeSum blocks *
        factor.word.weight PEAddres.weight) :=
  reweight (by rw [degree_positive_blocks])
    (positiveExponentExpansion hinputWeight factor
      (positiveSignedBlocks blocks)
      (by
        intro hnil
        have hzero : degreeSum blocks = 0 := by
          rw [← degree_positive_blocks blocks, hnil]
          rfl
        omega)
      (fun block hblock =>
        degree_pos_blocks hblock))

@[simp]
lemma block_exponent_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (factor : SPFactora H inputWeight)
    (blocks : List Block)
    (hdegree : 0 < degreeSum blocks) :
    (signedExponentExpansion
      hinputWeight factor blocks hdegree).eval =
        fun q : ℕ => signedBlockProduct (factor.exponent q) blocks := by
  rw [signedExponentExpansion, eval_reweight,
    positive_exponent_expansion]
  funext q
  exact signed_positive_blocks (factor.exponent q) blocks

/-- Normalize one weighted signed profile after substituting powered parents. -/
noncomputable def weightedProfileExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (left right : SPFactora H inputWeight)
    (profile : WBProf)
    (hleft : 0 < profile.profile.leftDegree)
    (hright : 0 < profile.profile.rightDegree) :
    BCExp inputWeight
      (profile.profile.leftDegree *
          left.word.weight PEAddres.weight +
        profile.profile.rightDegree *
          right.word.weight PEAddres.weight) :=
  reweight (by
      simp [SBProf.leftDegree, SBProf.rightDegree])
    (((signedExponentExpansion hinputWeight left
      profile.profile.leftBlocks
      (by simpa [SBProf.leftDegree] using hleft)).mul
        (signedExponentExpansion hinputWeight right
          profile.profile.rightBlocks
          (by simpa [SBProf.rightDegree] using hright))).scale
            profile.multiplicity)

@[simp]
lemma weighted_profile_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (left right : SPFactora H inputWeight)
    (profile : WBProf)
    (hleft : 0 < profile.profile.leftDegree)
    (hright : 0 < profile.profile.rightDegree) :
    (weightedProfileExpansion
      hinputWeight left right profile hleft hright).eval =
        fun q : ℕ =>
          weightedProfileValue profile
            (left.exponent q) (right.exponent q) := by
  funext q
  rw [weightedProfileExpansion, eval_reweight,
    BCExp.eval_scale,
    BCExp.eval_mul,
    block_exponent_expansion,
    block_exponent_expansion]
  rfl

/--
Normalize a homogeneous signed-profile list after substituting powered
parents.
-/
noncomputable def weightedProfilesExpansion
    {d inputWeight leftDegree rightDegree : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (left right : SPFactora H inputWeight)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree) :
    (profiles : List WBProf) →
      (∀ profile ∈ profiles,
        profile.profile.leftDegree = leftDegree) →
      (∀ profile ∈ profiles,
        profile.profile.rightDegree = rightDegree) →
      BCExp inputWeight
        (leftDegree * left.word.weight PEAddres.weight +
          rightDegree * right.word.weight PEAddres.weight)
  | [], _, _ =>
      BCExp.zero inputWeight
        (leftDegree * left.word.weight PEAddres.weight +
          rightDegree * right.word.weight PEAddres.weight)
  | profile :: profiles, hprofilesLeft, hprofilesRight =>
      (reweight (by
          rw [hprofilesLeft profile (by simp),
            hprofilesRight profile (by simp)])
        (weightedProfileExpansion hinputWeight left right profile
          (by rw [hprofilesLeft profile (by simp)]; exact hleft)
          (by rw [hprofilesRight profile (by simp)]; exact hright))).add
            (weightedProfilesExpansion hinputWeight left right
              hleft hright profiles
              (fun next hnext => hprofilesLeft next (by simp [hnext]))
              (fun next hnext => hprofilesRight next (by simp [hnext])))

@[simp]
lemma weighted_profiles_expansion
    {d inputWeight leftDegree rightDegree : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (left right : SPFactora H inputWeight)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree) :
    ∀ (profiles : List WBProf)
      (hprofilesLeft :
        ∀ profile ∈ profiles,
          profile.profile.leftDegree = leftDegree)
      (hprofilesRight :
        ∀ profile ∈ profiles,
          profile.profile.rightDegree = rightDegree),
      (weightedProfilesExpansion hinputWeight left right
        hleft hright profiles hprofilesLeft hprofilesRight).eval =
          fun q : ℕ =>
            (profiles.map fun profile =>
              weightedProfileValue profile
                (left.exponent q) (right.exponent q)).sum
  | [], _, _ => by
      exact BCExp.eval_zero _ _
  | profile :: profiles, hprofilesLeft, hprofilesRight => by
      funext q
      rw [weightedProfilesExpansion,
        BCExp.eval_add, eval_reweight,
        weighted_profile_expansion,
        weighted_profiles_expansion hinputWeight left right
          hleft hright profiles
          (fun next hnext => hprofilesLeft next (by simp [hnext]))
          (fun next hnext => hprofilesRight next (by simp [hnext]))]
      rfl

end BCExp

namespace CFSubsti
namespace HFPkt

/-- Substitute powered parents into one homogeneous signed-profile packet. -/
noncomputable def blockCoordinateExpansion
    {d inputWeight leftDegree rightDegree : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet : HFPkt leftDegree rightDegree)
    (hinputWeight : 0 < inputWeight)
    (left right : SPFactora H inputWeight)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree) :
    BCExp inputWeight
      (leftDegree * left.word.weight PEAddres.weight +
        rightDegree * right.word.weight PEAddres.weight) :=
  BCExp.weightedProfilesExpansion
    hinputWeight left right hleft hright packet.profiles
      packet.profiles_leftDegree packet.profiles_rightDegree

@[simp]
lemma block_coordinate_expansion
    {d inputWeight leftDegree rightDegree : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet : HFPkt leftDegree rightDegree)
    (hinputWeight : 0 < inputWeight)
    (left right : SPFactora H inputWeight)
    (hleft : 0 < leftDegree)
    (hright : 0 < rightDegree) :
    (packet.blockCoordinateExpansion
      hinputWeight left right hleft hright).eval =
        fun q : ℕ => packet.value (left.exponent q) (right.exponent q) := by
  rw [blockCoordinateExpansion,
    BCExp.weighted_profiles_expansion]
  rfl

end HFPkt
end CFSubsti

namespace SFSubstia

/-- Substitute two powered Hall words into one signed recollection packet. -/
def boundWord
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet : RFPkt)
    (left right : SPFactora H inputWeight) :
    CWord (HEAddres H) :=
  CWord.hallPairBind left.word right.word packet.word

@[simp]
lemma weight_boundWord
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet : RFPkt)
    (left right : SPFactora H inputWeight) :
    (boundWord packet left right).weight PEAddres.weight =
      packet.word.pairLeftDegree *
          left.word.weight PEAddres.weight +
        packet.word.pairRightDegree *
          right.word.weight PEAddres.weight := by
  rw [boundWord, CWord.weight_pair_bind,
    CWord.pair_atom_degree]

/-- Normalize the exponent carried by one substituted signed packet. -/
noncomputable def coefficientExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (packet : RFPkt)
    (left right : SPFactora H inputWeight) :
    BCExp inputWeight
      ((boundWord packet left right).weight PEAddres.weight) :=
  BCExp.reweight (by
      rw [weight_boundWord])
    (packet.profiles.blockCoordinateExpansion hinputWeight left right
      packet.positive.1 packet.positive.2)

@[simp]
lemma eval_coefficientExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (packet : RFPkt)
    (left right : SPFactora H inputWeight) :
    (coefficientExpansion hinputWeight packet left right).eval =
      fun q : ℕ => packet.profiles.value (left.exponent q) (right.exponent q) := by
  simp [coefficientExpansion]

/-- Attach one normalized signed packet exponent to its bound Hall word. -/
noncomputable def wordExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (packet : RFPkt)
    (left right : SPFactora H inputWeight) :
    SWExp H inputWeight where
  word := boundWord packet left right
  expansion := coefficientExpansion hinputWeight packet left right

@[simp]
lemma exponent_wordExpansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (packet : RFPkt)
    (left right : SPFactora H inputWeight) :
    (wordExpansion hinputWeight packet left right).exponent =
      fun q : ℕ => packet.profiles.value (left.exponent q) (right.exponent q) :=
  eval_coefficientExpansion hinputWeight packet left right

@[simp]
lemma word_eval_expansion
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (packet : RFPkt)
    (left right : SPFactora H inputWeight) :
    (wordExpansion hinputWeight packet left right).word.eval
        PEAddres.freeLowerTruncation =
      packet.word.eval
        (HPAtom.eval (left.wordValue (n := n)) (right.wordValue (n := n))) := by
  simp [wordExpansion, boundWord, SPFactora.wordValue,
    CWord.eval_pair_bind]

/-- Attach an ordered signed-profile packet list to two powered parents. -/
noncomputable def wordExpansions
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (packets : List RFPkt)
    (left right : SPFactora H inputWeight) :
    List (SWExp H inputWeight) :=
  packets.map fun packet => wordExpansion hinputWeight packet left right

/-- Evaluate a finite ordered list of substituted signed-profile packets. -/
lemma list_value_expansions
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (packets : List RFPkt)
    (left right : SPFactora H inputWeight)
    (q : ℕ) :
    SWExp.listValue (n := n) q
        (wordExpansions hinputWeight packets left right) =
      (packets.map fun packet =>
        packet.word.eval
            (HPAtom.eval
              (left.wordValue (n := n)) (right.wordValue (n := n))) ^
          packet.profiles.value (left.exponent q) (right.exponent q)).prod := by
  induction packets with
  | nil =>
      rfl
  | cons packet packets ih =>
      change
        (wordExpansion hinputWeight packet left right).word.eval
              PEAddres.freeLowerTruncation ^
            (wordExpansion hinputWeight packet left right).exponent q *
          SWExp.listValue q
            (wordExpansions hinputWeight packets left right) =
        _ * _
      rw [word_eval_expansion, exponent_wordExpansion, ih]
      rfl

/-- Every substituted expansion remembers its source signed packet. -/
lemma packet_word_expansions
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {hinputWeight : 0 < inputWeight}
    {packets : List RFPkt}
    {left right : SPFactora H inputWeight}
    {expansion : SWExp H inputWeight}
    (hexpansion : expansion ∈ wordExpansions hinputWeight packets left right) :
    ∃ packet ∈ packets,
      expansion = wordExpansion hinputWeight packet left right := by
  rcases List.mem_map.mp hexpansion with ⟨packet, hpacket, rfl⟩
  exact ⟨packet, hpacket, rfl⟩

/-- Every substituted signed packet lies strictly above its left parent. -/
lemma left_word_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (packet : RFPkt)
    (left right : SPFactora H inputWeight) :
    left.word.weight PEAddres.weight <
      (wordExpansion hinputWeight packet left right).word.weight
        PEAddres.weight := by
  rw [wordExpansion, weight_boundWord]
  refine lt_of_le_of_lt (Nat.le_mul_of_pos_left _ packet.positive.1) ?_
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos packet.positive.2 right.word_weight_pos)

/-- Every substituted signed packet lies strictly above its right parent. -/
lemma right_word_expansion
    {d inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (hinputWeight : 0 < inputWeight)
    (packet : RFPkt)
    (left right : SPFactora H inputWeight) :
    right.word.weight PEAddres.weight <
      (wordExpansion hinputWeight packet left right).word.weight
        PEAddres.weight := by
  rw [wordExpansion, weight_boundWord]
  refine lt_of_le_of_lt (Nat.le_mul_of_pos_left _ packet.positive.2) ?_
  rw [Nat.add_comm]
  exact Nat.lt_add_of_pos_right
    (Nat.mul_pos packet.positive.1 left.word_weight_pos)

end SFSubstia

namespace CFExp
namespace TAInt

/--
A cutoff signed-profile packet compiles to the powered correction factory
needed at every support stratum.
-/
noncomputable def powerSupportedFactory
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet : TAInt.{u} d n)
    (hinputWeight : 0 < inputWeight)
    (lowerWeight : ℕ) :
    SEFtry
      (n := n) (inputWeight := inputWeight) H lowerWeight where
  wordExpansions left right _hleft _hright :=
    SFSubstia.wordExpansions
      hinputWeight packet.packets left right
  listValue_eq left right _hleft _hright q := by
    rw [SFSubstia.list_value_expansions]
    simpa [SPFactora.eval] using
      packet.listEval_eq (left.wordValue (n := n)) (right.wordValue (n := n))
        (left.exponent q) (right.exponent q)
  word_weight_left left right _hleft _hright expansion hexpansion := by
    rcases
        SFSubstia.packet_word_expansions
          hexpansion with
      ⟨nextPacket, _hnextPacket, rfl⟩
    exact
      SFSubstia.left_word_expansion
        hinputWeight nextPacket left right
  word_weight_right left right _hleft _hright expansion hexpansion := by
    rcases
        SFSubstia.packet_word_expansions
          hexpansion with
      ⟨nextPacket, _hnextPacket, rfl⟩
    exact
      SFSubstia.right_word_expansion
        hinputWeight nextPacket left right

end TAInt

namespace UAPkt

/--
A universal signed-profile packet specializes to the powered correction
factory at every lower-central cutoff.
-/
noncomputable def powerSupportedFactory
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (packet : UAPkt.{u})
    (hinputWeight : 0 < inputWeight)
    (lowerWeight : ℕ) :
    SEFtry
      (n := n) (inputWeight := inputWeight) H lowerWeight :=
  (packet.truncatedAllIntegral (d := d) (n := n))
    |>.powerSupportedFactory hinputWeight lowerWeight

end UAPkt
end CFExp

end TCTex
end Submission

import Submission.Group.Zassenhaus.CompletePetrescoRecipe
import Submission.Group.Zassenhaus.SymbolicHallCollection

/-!
# Atomic Hall-Petresco packets in the class-two zone

Near the lower-central cutoff, a powered commutator has no retained nested
errors.  It is either trivial, or it is represented by the single complete
basic block recipe.  This supplies the terminal case for a recursive
nonterminal product and inverse collector while retaining raw-block history.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace BRSpec
namespace TAPktb

/--
In the class-two zone, both raw Hall atoms commute with their leading
commutator in the nilpotent truncation quotient.
-/
lemma commute_basic_two
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (leftAddress rightAddress : HEAddres H)
    (hleft :
      n ≤ 2 * leftAddress.1 + rightAddress.1)
    (hright :
      n ≤ leftAddress.1 + 2 * rightAddress.1) :
    Commute
        (HEAddres.freeLowerTruncation
          (n := n) leftAddress)
        ⁅HEAddres.freeLowerTruncation
            (n := n) leftAddress,
          HEAddres.freeLowerTruncation
            (n := n) rightAddress⁆ ∧
      Commute
        (HEAddres.freeLowerTruncation
          (n := n) rightAddress)
        ⁅HEAddres.freeLowerTruncation
            (n := n) leftAddress,
          HEAddres.freeLowerTruncation
            (n := n) rightAddress⁆ := by
  let x :=
    HEAddres.freeLowerTruncation
      (n := n) leftAddress
  let y :=
    HEAddres.freeLowerTruncation
      (n := n) rightAddress
  let leftWeight := leftAddress.1
  let rightWeight := rightAddress.1
  have hleftWeight : 0 < leftWeight := by
    simpa [leftWeight, HEAddres.weight] using
      HEAddres.weight_pos leftAddress
  have hrightWeight : 0 < rightWeight := by
    simpa [rightWeight, HEAddres.weight] using
      HEAddres.weight_pos rightAddress
  have hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (leftWeight - 1) := by
    simpa [x, leftWeight, HEAddres.weight] using
      HEAddres.free_truncation_series
        (n := n) leftAddress
  have hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (rightWeight - 1) := by
    simpa [y, rightWeight, HEAddres.weight] using
      HEAddres.free_truncation_series
        (n := n) rightAddress
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        ((leftWeight - 1) + (rightWeight - 1) + 1) :=
    element_lower_series hx hy
  have hxx :
      ⁅x, ⁅x, y⁆⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        ((leftWeight - 1) + ((leftWeight - 1) + (rightWeight - 1) + 1) + 1) :=
    element_lower_series hx hxy
  have hyy :
      ⁅y, ⁅x, y⁆⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        ((rightWeight - 1) + ((leftWeight - 1) + (rightWeight - 1) + 1) + 1) :=
    element_lower_series hy hxy
  have hxxOne : ⁅x, ⁅x, y⁆⁆ = 1 := by
    apply eq_bot_iff.mp
      SCFactor.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by
      dsimp [leftWeight, rightWeight] at hleft hright ⊢
      omega) hxx
  have hyyOne : ⁅y, ⁅x, y⁆⁆ = 1 := by
    apply eq_bot_iff.mp
      SCFactor.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by
      dsimp [leftWeight, rightWeight] at hleft hright ⊢
      omega) hyy
  constructor
  · rw [← commutatorElement_eq_one_iff_commute]
    simpa [x, y] using hxxOne
  · rw [← commutatorElement_eq_one_iff_commute]
    simpa [x, y] using hyyOne

/-- At total weight at least the cutoff, the atomic packet is empty. -/
def empty_n_add
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (leftAddress rightAddress : HEAddres H)
    (hcutoff : n ≤ leftAddress.1 + rightAddress.1) :
    TAPktb (n := n) H leftAddress rightAddress where
  recipes := []
  listEval_eq := by
    intro leftExponent rightExponent
    simp only [List.map_nil, List.prod_nil]
    symm
    apply eq_bot_iff.mp
      SCFactor.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by
      have hleftWeight := HEAddres.weight_pos leftAddress
      have hrightWeight := HEAddres.weight_pos rightAddress
      dsimp [HEAddres.weight] at hleftWeight hrightWeight
      omega)
      (element_lower_series
        ((Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (leftAddress.1 - 1)).zpow_mem
            (HEAddres.free_truncation_series
              (n := n) leftAddress)
            leftExponent)
        ((Subgroup.lowerCentralSeries
          (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
          (rightAddress.1 - 1)).zpow_mem
            (HEAddres.free_truncation_series
              (n := n) rightAddress)
            rightExponent))
  word_weight_cutoff := by
    simp

/--
If the leading bracket survives but both nested brackets vanish, the atomic
packet is the singleton basic recipe.
-/
def singleton_basic_two
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (leftAddress rightAddress : HEAddres H)
    (hcutoff : leftAddress.1 + rightAddress.1 < n)
    (hleft :
      n ≤ 2 * leftAddress.1 + rightAddress.1)
    (hright :
      n ≤ leftAddress.1 + 2 * rightAddress.1) :
    TAPktb (n := n) H leftAddress rightAddress where
  recipes := [hallPair]
  listEval_eq := by
    intro leftExponent rightExponent
    have hcommutes :=
      commute_basic_two leftAddress rightAddress hleft hright
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      mul_one, erased_shape_pair, coefficient_value_pair,
      CWord.eval_pair_base]
    have hpullLeft :
        ⁅HEAddres.freeLowerTruncation
              (n := n) leftAddress ^ leftExponent,
            HEAddres.freeLowerTruncation
              (n := n) rightAddress⁆ =
          ⁅HEAddres.freeLowerTruncation
              (n := n) leftAddress,
            HEAddres.freeLowerTruncation
              (n := n) rightAddress⁆ ^ leftExponent :=
      commutator_zpow_commute
        hcommutes.1 leftExponent
    have hcommuteRight :
        Commute
          (HEAddres.freeLowerTruncation
            (n := n) rightAddress)
          ⁅HEAddres.freeLowerTruncation
                (n := n) leftAddress ^ leftExponent,
            HEAddres.freeLowerTruncation
              (n := n) rightAddress⁆ := by
      rw [hpullLeft]
      exact hcommutes.2.zpow_right leftExponent
    rw [zpow_commute_collection
      hcommuteRight, hpullLeft, zpow_mul]
  word_weight_cutoff := by
    intro R hR
    rcases List.mem_singleton.mp hR with rfl
    simpa using hcutoff

/--
In the class-two zone, choose the empty or singleton-basic recipe packet
according to whether the leading bracket itself survives.
-/
def of_classTwo
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (leftAddress rightAddress : HEAddres H)
    (hleft :
      n ≤ 2 * leftAddress.1 + rightAddress.1)
    (hright :
      n ≤ leftAddress.1 + 2 * rightAddress.1) :
    TAPktb (n := n) H leftAddress rightAddress :=
  if hcutoff : n ≤ leftAddress.1 + rightAddress.1 then
    empty_n_add leftAddress rightAddress hcutoff
  else
    singleton_basic_two leftAddress rightAddress
      (Nat.lt_of_not_ge hcutoff) hleft hright

end TAPktb
end BRSpec

namespace TSPkt

/--
Build the terminal polynomial correction packet for two raw atomic source
factors directly from the class-two inequalities.
-/
def atomic_sources_two
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (hleft :
      n ≤ 2 * leftAddress.1 + rightAddress.1)
    (hright :
      n ≤ leftAddress.1 + 2 * rightAddress.1) :
    TSPkt n
      (.source leftInput leftAddress) (.source rightInput rightAddress) :=
  (BRSpec.TAPktb.of_classTwo
    leftAddress rightAddress hleft hright).toCorrectionPacket
      leftInput rightInput

end TSPkt

/-- Perform one terminal class-two swap between two raw atomic source factors. -/
def TCStepa.obstruction_atomicsources_classtwo
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {ι : Type}
    (P S : List (SPFactor H ι))
    (leftInput rightInput : ι)
    (leftAddress rightAddress : HEAddres H)
    (hleft :
      n ≤ 2 * leftAddress.1 + rightAddress.1)
    (hright :
      n ≤ leftAddress.1 + 2 * rightAddress.1) :
    TCStepa (n := n) H ι
      (P ++
        [.source leftInput leftAddress, .source rightInput rightAddress] ++ S)
      (P ++
        (TSPkt.atomic_sources_two
          leftInput rightInput leftAddress rightAddress hleft hright).factors ++
        [.source rightInput rightAddress, .source leftInput leftAddress] ++ S) :=
  TCStepa.obstruction P S
    (.source leftInput leftAddress) (.source rightInput rightAddress)
    (TSPkt.atomic_sources_two
      leftInput rightInput leftAddress rightAddress hleft hright)

end TCTex
end Submission

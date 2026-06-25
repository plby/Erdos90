import Submission.Group.Zassenhaus.CollectionSteps

/-!
# Concrete correction packets near the truncation cutoff

Once nested commutators have reached the defining lower-central cutoff, a
powered commutator is exactly its leading bracket raised to the product of the
two exponents.  This supplies the first nontrivial concrete
`SHPkt`: a singleton bracket packet.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

/--
If `y` commutes with its commutator with `x`, integral powers in the right
input pull out of the commutator.
-/
lemma element_zpow_commute
    {G : Type*} [Group G]
    {x y : G}
    (hcomm : Commute y ⁅x, y⁆) :
    ∀ m : ℤ, ⁅x, y ^ m⁆ = ⁅x, y⁆ ^ m
  | .ofNat m => by
      simpa only [Int.ofNat_eq_natCast, zpow_natCast] using
        commutator_element_commute hcomm m
  | .negSucc m => by
      have hinv :
          ⁅x, y⁻¹⁆ = ⁅x, y⁆⁻¹ := by
        calc
          ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
            simp only [commutatorElement_def, inv_inv, mul_inv_rev]
            group
          _ = ⁅x, y⁆⁻¹ := by
            rw [(hcomm.inv_left.inv_right).eq]
            simp
      have hcommInv :
          Commute y⁻¹ ⁅x, y⁻¹⁆ := by
        rw [hinv]
        exact hcomm.inv_left.inv_right
      simpa only [zpow_negSucc, ← inv_pow, hinv] using
        commutator_element_commute hcommInv (m + 1)

namespace SHPkt

/--
If both inputs commute with their leading commutator, the singleton symbolic
bracket evaluates to the full commutator of the evaluated power factors.
-/
lemma singleton_bracket_commute
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    (B A : SPFactora H inputWeight)
    (hB :
      Commute (B.wordValue (n := n))
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆)
    (hA :
      Commute (A.wordValue (n := n))
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆)
    (q : ℕ) :
    (B.bracket A).eval (n := n) q =
      ⁅B.eval (n := n) q, A.eval (n := n) q⁆ := by
  rw [B.eval_bracket A q]
  change
    ⁅B.wordValue (n := n), A.wordValue (n := n)⁆ ^
        (B.exponent q * A.exponent q) =
      ⁅B.wordValue (n := n) ^ B.exponent q,
        A.wordValue (n := n) ^ A.exponent q⁆
  have hleft :
      ⁅B.wordValue (n := n) ^ B.exponent q, A.wordValue (n := n)⁆ =
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆ ^ B.exponent q :=
    commutator_zpow_commute hB (B.exponent q)
  have hright :
      Commute (A.wordValue (n := n))
        ⁅B.wordValue (n := n) ^ B.exponent q, A.wordValue (n := n)⁆ := by
    rw [hleft]
    exact hA.zpow_right (B.exponent q)
  rw [element_zpow_commute hright, hleft, zpow_mul]

/-- The class-two powered interchange is represented by one bracket factor. -/
def bracket_commute
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    (B A : SPFactora H inputWeight)
    (hB :
      Commute (B.wordValue (n := n))
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆)
    (hA :
      Commute (A.wordValue (n := n))
        ⁅B.wordValue (n := n), A.wordValue (n := n)⁆) :
    SHPkt n B A :=
  singletonBracket B A fun q =>
    singleton_bracket_commute B A hB hA q

/--
Near the lower-central cutoff the two nested commutators vanish, so the exact
powered interchange packet is the singleton bracket.
-/
def singleton_bracket_two
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    (B A : SPFactora H inputWeight)
    (hleft :
      n ≤
        2 * B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight)
    (hright :
      n ≤
        B.word.weight PEAddres.weight +
          2 * A.word.weight PEAddres.weight) :
    SHPkt n B A := by
  let x := B.wordValue (n := n)
  let y := A.wordValue (n := n)
  let bWeight := B.word.weight PEAddres.weight
  let aWeight := A.word.weight PEAddres.weight
  have hbWeight : 0 < bWeight := by
    simpa [bWeight] using B.word_weight_pos
  have haWeight : 0 < aWeight := by
    simpa [aWeight] using A.word_weight_pos
  have hx :
      x ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (bWeight - 1) := by
    simpa [x, bWeight] using B.value_lower_series (n := n)
  have hy :
      y ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        (aWeight - 1) := by
    simpa [y, aWeight] using A.value_lower_series (n := n)
  have hxy :
      ⁅x, y⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        ((bWeight - 1) + (aWeight - 1) + 1) :=
    element_lower_series hx hy
  have hxx :
      ⁅x, ⁅x, y⁆⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        ((bWeight - 1) + ((bWeight - 1) + (aWeight - 1) + 1) + 1) :=
    element_lower_series hx hxy
  have hyy :
      ⁅y, ⁅x, y⁆⁆ ∈ Subgroup.lowerCentralSeries
        (LowerCentralTruncation (FreeGroup (FreeGenerator.{u} d)) n)
        ((aWeight - 1) + ((bWeight - 1) + (aWeight - 1) + 1) + 1) :=
    element_lower_series hy hxy
  have hxxOne : ⁅x, ⁅x, y⁆⁆ = 1 := by
    apply eq_bot_iff.mp
      SPFactora.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by omega) hxx
  have hyyOne : ⁅y, ⁅x, y⁆⁆ = 1 := by
    apply eq_bot_iff.mp
      SPFactora.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by omega) hyy
  apply bracket_commute B A
  · rw [← commutatorElement_eq_one_iff_commute]
    simpa [x, y] using hxxOne
  · rw [← commutatorElement_eq_one_iff_commute]
    simpa [x, y] using hyyOne

end SHPkt

/-- A left input at the cutoff swaps past its neighbor without corrections. -/
def SCStepa.obstrucempty_nle_wordweightleft
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    (P S : List (SPFactora H inputWeight))
    (B A : SPFactora H inputWeight)
    (hB : n ≤ B.word.weight PEAddres.weight) :
    SCStepa H inputWeight n
      (P ++ [B, A] ++ S)
      (P ++ [A, B] ++ S) := by
  simpa using
    SCStepa.obstruction P S B A
      (SHPkt.empty_n_left B A hB)

/-- A right input at the cutoff swaps past its neighbor without corrections. -/
def SCStepa.obstrucempty_nle_wordweightright
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    (P S : List (SPFactora H inputWeight))
    (B A : SPFactora H inputWeight)
    (hA : n ≤ A.word.weight PEAddres.weight) :
    SCStepa H inputWeight n
      (P ++ [B, A] ++ S)
      (P ++ [A, B] ++ S) := by
  simpa using
    SCStepa.obstruction P S B A
      (SHPkt.empty_n_right B A hA)

/-- A class-two adjacent swap emits exactly one leading bracket correction. -/
def SCStepa.obstruction_singletbracket_classtwo
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {inputWeight : ℕ}
    (P S : List (SPFactora H inputWeight))
    (B A : SPFactora H inputWeight)
    (hleft :
      n ≤
        2 * B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight)
    (hright :
      n ≤
        B.word.weight PEAddres.weight +
          2 * A.word.weight PEAddres.weight) :
    SCStepa H inputWeight n
      (P ++ [B, A] ++ S)
      (P ++ [B.bracket A, A, B] ++ S) := by
  simpa using
    SCStepa.obstruction P S B A
      (SHPkt.singleton_bracket_two
        B A hleft hright)

end TCTex
end Submission

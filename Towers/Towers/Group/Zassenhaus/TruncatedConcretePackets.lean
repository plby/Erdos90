import Towers.Group.Zassenhaus.ConcretePackets
import Towers.Group.Zassenhaus.Recursion

/-!
# Concrete truncated correction packets for symbolic Hall powers

At the top of the lower-central filtration, powered commutators have no room
for higher errors.  The physically truncated repeated-power collector can
therefore choose automa between an empty packet and the singleton
leading bracket.

The file is intentionally not imported by the existing collection proof.
-/

namespace Towers
namespace TCTex

universe u

open scoped commutatorElement

namespace TCPkt

/-- A trivial evaluated commutator needs no retained repeated-power factors. -/
def empty_commutator_one
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (B A : SPFactora H inputWeight)
    (hcommutator :
      ∀ q : ℕ, ⁅B.eval (n := n) q, A.eval (n := n) q⁆ = 1) :
    TCPkt n B A where
  factors := []
  listEval_eq q := by
    simpa using (hcommutator q).symm
  word_weight_left x hx := by
    simp at hx
  word_weight_right x hx := by
    simp at hx
  word_weight_cutoff x hx := by
    simp at hx

/--
If the parent weights sum to the cutoff, their evaluated commutator vanishes in
the truncation quotient.
-/
def empty_n_weight
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (B A : SPFactora H inputWeight)
    (hsum :
      n ≤ B.word.weight PEAddres.weight +
        A.word.weight PEAddres.weight) :
    TCPkt n B A :=
  empty_commutator_one B A fun q => by
    apply eq_bot_iff.mp
      SPFactora.trunc_last_bot
    exact Subgroup.lowerCentralSeries_antitone (by
      have hB := B.word_weight_pos
      have hA := A.word_weight_pos
      omega)
      (element_lower_series
        (B.eval_lower_series q)
        (A.eval_lower_series q))

/--
In the class-two terminal zone, when the leading bracket survives the cutoff,
the exact truncated packet is its singleton.
-/
def singleton_bracket_two
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (B A : SPFactora H inputWeight)
    (hcutoff :
      B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight < n)
    (hleft :
      n ≤
        2 * B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight)
    (hright :
      n ≤
        B.word.weight PEAddres.weight +
          2 * A.word.weight PEAddres.weight) :
    TCPkt n B A where
  factors := [B.bracket A]
  listEval_eq :=
    (SHPkt.singleton_bracket_two
      B A hleft hright).listEval_eq
  word_weight_left x hx := by
    rcases List.mem_singleton.mp hx with rfl
    exact B.word_bracket_left A
  word_weight_right x hx := by
    rcases List.mem_singleton.mp hx with rfl
    exact B.word_bracket_right A
  word_weight_cutoff x hx := by
    rcases List.mem_singleton.mp hx with rfl
    simpa using hcutoff

/--
In the class-two zone, choose automa between an empty packet and the
singleton leading bracket according to whether that bracket survives.
-/
def of_classTwo
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (B A : SPFactora H inputWeight)
    (hleft :
      n ≤
        2 * B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight)
    (hright :
      n ≤
        B.word.weight PEAddres.weight +
          2 * A.word.weight PEAddres.weight) :
    TCPkt n B A :=
  if hcutoff :
      n ≤ B.word.weight PEAddres.weight +
        A.word.weight PEAddres.weight then
    empty_n_weight B A hcutoff
  else
    singleton_bracket_two B A (Nat.lt_of_not_ge hcutoff) hleft hright

/--
If three times the smaller parent weight reaches the cutoff, the repeated-power
obstruction is already in the class-two terminal zone.
-/
def n_min_weight
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (B A : SPFactora H inputWeight)
    (hterminal :
      n ≤ 3 * min
        (B.word.weight PEAddres.weight)
        (A.word.weight PEAddres.weight)) :
    TCPkt n B A :=
  of_classTwo B A
    (by
      have hminB :
          min
              (B.word.weight PEAddres.weight)
              (A.word.weight PEAddres.weight) ≤
            B.word.weight PEAddres.weight :=
        Nat.min_le_left _ _
      have hminA :
          min
              (B.word.weight PEAddres.weight)
              (A.word.weight PEAddres.weight) ≤
            A.word.weight PEAddres.weight :=
        Nat.min_le_right _ _
      omega)
    (by
      have hminB :
          min
              (B.word.weight PEAddres.weight)
              (A.word.weight PEAddres.weight) ≤
            B.word.weight PEAddres.weight :=
        Nat.min_le_left _ _
      have hminA :
          min
              (B.word.weight PEAddres.weight)
              (A.word.weight PEAddres.weight) ≤
            A.word.weight PEAddres.weight :=
        Nat.min_le_right _ _
      omega)

end TCPkt

/-- An obstruction at total weight at least the cutoff swaps without corrections. -/
def TSStep.obstrucempty_nle_addwordweight
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (P S : List (SPFactora H inputWeight))
    (B A : SPFactora H inputWeight)
    (hsum :
      n ≤ B.word.weight PEAddres.weight +
        A.word.weight PEAddres.weight) :
    TSStep (n := n) H inputWeight
      (P ++ [B, A] ++ S)
      (P ++ [A, B] ++ S) := by
  simpa using
    TSStep.obstruction P S B A
      (TCPkt.empty_n_weight
        B A hsum)

/-- A class-two adjacent swap emits exactly one surviving bracket correction. -/
def TSStep.obstruction_singletbracket_classtwo
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    (P S : List (SPFactora H inputWeight))
    (B A : SPFactora H inputWeight)
    (hcutoff :
      B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight < n)
    (hleft :
      n ≤
        2 * B.word.weight PEAddres.weight +
          A.word.weight PEAddres.weight)
    (hright :
      n ≤
        B.word.weight PEAddres.weight +
          2 * A.word.weight PEAddres.weight) :
    TSStep (n := n) H inputWeight
      (P ++ [B, A] ++ S)
      (P ++ [B.bracket A, A, B] ++ S) := by
  simpa using
    TSStep.obstruction P S B A
      (TCPkt.singleton_bracket_two
        B A hcutoff hleft hright)

/-- Perform a class-two terminal swap with its automatic empty-or-singleton packet. -/
def TSStep.obstruction_class_two
    {d n inputWeight : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
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
    TSStep (n := n) H inputWeight
      (P ++ [B, A] ++ S)
      (P ++
        (TCPkt.of_classTwo
          B A hleft hright).factors ++ [A, B] ++ S) :=
  TSStep.obstruction P S B A
    (TCPkt.of_classTwo B A hleft hright)

end TCTex
end Towers

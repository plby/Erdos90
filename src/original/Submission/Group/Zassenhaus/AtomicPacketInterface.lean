import Submission.Group.Zassenhaus.PositiveDegreeRecipes
import Submission.Group.Zassenhaus.SymbolicHallSteps

/-!
# Atomic Hall-Petresco packet interface for product and inverse collection

The nonterminal Claim 8 collector must preserve independent raw-block
histories until it reaches a finite endpoint list.  A packet of complete
`BRecipe`s is the correct compression boundary: every recipe then becomes
one explicit generalized-binomial polynomial factor.

This file isolates the remaining Hall-Petresco obligation for a pair of raw
Hall-coordinate atoms and turns any solution into the cutoff-specific symbolic
correction packet consumed by the collection rewrite relation.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement
open HACoeff

namespace BRSpec

/--
A finite cutoff-specific Hall-Petresco expansion for two raw Hall-coordinate
atoms.  Its recipes retain complete independent-block histories, while its
evaluation law is parametrized by arbitrary integral source exponents.
-/
structure TAPktb
    {d n : ℕ}
    (H : ∀ r : ℕ, BCWta.{u} d r)
    (leftAddress rightAddress : HEAddres H) where
  recipes :
    List BRecipe
  listEval_eq :
    ∀ leftExponent rightExponent : ℤ,
      (recipes.map fun R =>
        R.erasedShape.eval
            (HPAtom.eval
              (HEAddres.freeLowerTruncation
                (n := n) leftAddress)
              (HEAddres.freeLowerTruncation
                (n := n) rightAddress)) ^
          coefficientValue R leftExponent rightExponent).prod =
        ⁅HEAddres.freeLowerTruncation
              (n := n) leftAddress ^ leftExponent,
          HEAddres.freeLowerTruncation
              (n := n) rightAddress ^ rightExponent⁆
  word_weight_cutoff :
    ∀ R ∈ recipes,
      R.leftDegree * leftAddress.1 + R.rightDegree * rightAddress.1 < n

namespace TAPktb

/-- Attach the packet's complete block recipes to two raw input labels. -/
def factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {leftAddress rightAddress : HEAddres H}
    (packet : TAPktb (n := n) H leftAddress rightAddress)
    {ι : Type}
    (leftInput rightInput : ι) :
    List (SPFactor H ι) :=
  symbolicFactors packet.recipes leftInput rightInput
    leftAddress rightAddress

/-- Attached endpoint factors evaluate to the required powered commutator. -/
lemma listEval_factors
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {leftAddress rightAddress : HEAddres H}
    (packet : TAPktb (n := n) H leftAddress rightAddress)
    {ι : Type}
    (e : ι → HEFam H)
    (leftInput rightInput : ι) :
    SPFactor.listEval (n := n) e
        (packet.factors leftInput rightInput) =
      ⁅(SPFactor.source leftInput leftAddress).eval
          (n := n) e,
        (SPFactor.source rightInput rightAddress).eval
          (n := n) e⁆ := by
  rw [factors, listSymbolicFactors]
  simpa using
    packet.listEval_eq
      (e leftInput leftAddress.1 leftAddress.2)
      (e rightInput rightAddress.1 rightAddress.2)

/--
Any finite atomic Hall-Petresco recipe packet supplies the exact truncated
polynomial correction packet required for one adjacent symbolic swap.
-/
def toCorrectionPacket
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {leftAddress rightAddress : HEAddres H}
    (packet : TAPktb (n := n) H leftAddress rightAddress)
    {ι : Type}
    (leftInput rightInput : ι) :
    TSPkt n
      (.source leftInput leftAddress) (.source rightInput rightAddress) where
  factors := packet.factors leftInput rightInput
  listEval_eq e := packet.listEval_factors e leftInput rightInput
  word_weight_left := by
    intro x hx
    rcases recipe_factors hx with ⟨R, _hR, rfl⟩
    exact left_address_factor
      R leftInput rightInput leftAddress rightAddress
  word_weight_right := by
    intro x hx
    rcases recipe_factors hx with ⟨R, _hR, rfl⟩
    exact right_address_factor
      R leftInput rightInput leftAddress rightAddress
  word_weight_cutoff := by
    intro x hx
    rcases recipe_factors hx with ⟨R, hR, rfl⟩
    rw [word_symbolic_factor]
    exact packet.word_weight_cutoff R hR

/-- Use an atomic recipe packet as one adjacent polynomial collection move. -/
def toCollectionStep
    {d n : ℕ}
    {H : ∀ r : ℕ, BCWta.{u} d r}
    {leftAddress rightAddress : HEAddres H}
    (packet : TAPktb (n := n) H leftAddress rightAddress)
    {ι : Type}
    (P S : List (SPFactor H ι))
    (leftInput rightInput : ι) :
    TCStepa (n := n) H ι
      (P ++
        [.source leftInput leftAddress, .source rightInput rightAddress] ++ S)
      (P ++ packet.factors leftInput rightInput ++
        [.source rightInput rightAddress, .source leftInput leftAddress] ++ S) :=
  TCStepa.obstruction P S
    (.source leftInput leftAddress) (.source rightInput rightAddress)
    (packet.toCorrectionPacket leftInput rightInput)

end TAPktb
end BRSpec
end TCTex
end Submission

import Submission.Group.Zassenhaus.OuterBracketWorklist
import Submission.Group.Zassenhaus.SemanticPacketFactories
import Submission.Group.Zassenhaus.FactorSourceReduction

/-!
# Powered packet worklists for brackets with finite left products

The unrestricted group-level outer-bracket worklist retains conjugations.
For symbolic Hall powers, each terminal commutator in that worklist is
represented by an existing truncated Hall-Petresco correction packet.

This file packages the resulting finite symbolic source.  Its evaluation is
exactly the bracket of the evaluated left source with one fixed powered
factor.  It also preserves a common lower support bound and physical
truncation.

The file is intentionally not imported by the existing collection proof.
-/

namespace Submission
namespace TCTex

universe u

open scoped commutatorElement

namespace PBWork

/--
Replace every terminal bracket in the unrestricted left-product worklist by
its truncated powered correction packet.
-/
def factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (right : SPFactora H inputWeight)
    (packet :
      ∀ left : SPFactora H inputWeight,
        TCPkt n left right) :
    List (SPFactora H inputWeight) →
      List (SPFactora H inputWeight)
  | [] => []
  | left :: tail =>
      [left] ++ factors right packet tail ++ [left.neg] ++
        (packet left).factors

@[simp]
theorem factors_nil
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (right : SPFactora H inputWeight)
    (packet :
      ∀ left : SPFactora H inputWeight,
        TCPkt n left right) :
    factors right packet [] = [] :=
  rfl

@[simp]
theorem factors_cons
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (right left : SPFactora H inputWeight)
    (packet :
      ∀ x : SPFactora H inputWeight,
        TCPkt n x right)
    (tail : List (SPFactora H inputWeight)) :
    factors right packet (left :: tail) =
      [left] ++ factors right packet tail ++ [left.neg] ++
        (packet left).factors :=
  rfl

/--
The symbolic powered worklist evaluates exactly to the bracket of the
evaluated left source with the fixed outer-right factor.
-/
theorem listEval_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (right : SPFactora H inputWeight)
    (packet :
      ∀ left : SPFactora H inputWeight,
        TCPkt n left right)
    (q : ℕ) :
    ∀ left : List (SPFactora H inputWeight),
      SPFactora.listEval (n := n) q
          (factors right packet left) =
        ⁅SPFactora.listEval (n := n) q left,
          right.eval (n := n) q⁆ := by
  intro left
  induction left with
  | nil =>
      simp [SPFactora.listEval]
  | cons head tail ih =>
      rw [factors_cons]
      simp only [SPFactora.listEval_append,
        SPFactora.listEval_cons,
        SPFactora.listEval_nil, mul_one,
        SPFactora.eval_neg, ih, (packet head).listEval_eq]
      rw [element_mul_left]

/-- The symbolic worklist preserves any common lower support bound. -/
theorem weight_least_factors
    {d n inputWeight lowerWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (right : SPFactora H inputWeight)
    (packet :
      ∀ left : SPFactora H inputWeight,
        TCPkt n left right) :
    ∀ {left : List (SPFactora H inputWeight)},
      SPFactora.WordWeightLeast lowerWeight left →
        SPFactora.WordWeightLeast lowerWeight
          (factors right packet left) := by
  intro left hleft
  induction left with
  | nil =>
      intro x hx
      simp at hx
  | cons head tail ih =>
      have hhead :
          lowerWeight ≤ head.word.weight PEAddres.weight :=
        hleft head (by simp)
      have htail :
          SPFactora.WordWeightLeast lowerWeight tail := by
        intro x hx
        exact hleft x (by simp [hx])
      intro x hx
      simp only [factors_cons, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with ((rfl | hx) | rfl) | hx
      · exact hhead
      · exact ih htail x hx
      · simpa only [SPFactora.word_neg] using hhead
      · exact
          hhead.trans
            (Nat.le_of_lt ((packet head).word_weight_left x hx))

/-- The symbolic worklist is physically truncated when its left source is. -/
theorem isTruncated_factors
    {d n inputWeight : ℕ}
    {H : ∀ s : ℕ, BCWta.{u} d s}
    (right : SPFactora H inputWeight)
    (packet :
      ∀ left : SPFactora H inputWeight,
        TCPkt n left right) :
    ∀ {left : List (SPFactora H inputWeight)},
      SPFactora.IsTruncated n left →
        SPFactora.IsTruncated n
          (factors right packet left) := by
  intro left hleft
  induction left with
  | nil =>
      intro x hx
      simp at hx
  | cons head tail ih =>
      have hhead :
          head.word.weight PEAddres.weight < n :=
        hleft head (by simp)
      have htail : SPFactora.IsTruncated n tail := by
        intro x hx
        exact hleft x (by simp [hx])
      intro x hx
      simp only [factors_cons, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hx
      rcases hx with ((rfl | hx) | rfl) | hx
      · exact hhead
      · exact ih htail x hx
      · simpa only [SPFactora.word_neg] using hhead
      · exact (packet head).word_weight_cutoff x hx

end PBWork
end TCTex
end Submission

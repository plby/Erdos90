import Submission.ClassField.Shifting.LowDegreeSequence
import Submission.ClassField.Shifting.TateLowerShift

/-!
# Milne, Class Field Theory, Theorem II.3.11: the double dimension shift

This file formalizes the splice at the end of Tate's proof.  Two short exact
sequences with acyclic middle terms, whose adjacent terms are isomorphic,
give a two-degree shift in positive cohomology and in positive homology.
-/

namespace Submission.CField.Shifting

open CategoryTheory CategoryTheory.Limits Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

/-- The homological dimension shift associated to a short exact sequence
with positive-homology-acyclic middle term. -/
noncomputable def homologyShiftingIso
    {X : ShortComplex (Rep.{u} k G)} (hX : X.ShortExact)
    (hacyclic : ∀ n : ℕ, 0 < n → IsZero (groupHomology X.X₂ n))
    (n : ℕ) (hn : 0 < n) :
    groupHomology X.X₃ (n + 1) ≅ groupHomology X.X₁ n := by
  let d := groupHomology.δ hX (n + 1) n rfl
  let hd : IsIso d :=
    groupHomology.isIso_δ_of_isZero hX n
      (hacyclic (n + 1) (Nat.succ_pos n)) (hacyclic n hn)
  exact @asIso _ _ _ _ d hd

/-- Splicing two cohomological dimension shifts raises degree by two.  The
isomorphism `e` identifies the quotient in the first sequence with the kernel
in the second sequence. -/
noncomputable def positiveDoubleShift
    {X Y : ShortComplex (Rep.{u} k G)}
    (hX : X.ShortExact) (hY : Y.ShortExact)
    (e : Y.X₁ ≅ X.X₃)
    (hXacyclic : ∀ n : ℕ, 0 < n → IsZero (groupCohomology X.X₂ n))
    (hYacyclic : ∀ n : ℕ, 0 < n → IsZero (groupCohomology Y.X₂ n))
    (n : ℕ) (hn : 0 < n) :
    groupCohomology Y.X₃ n ≅ groupCohomology X.X₁ (n + 2) := by
  simpa [Nat.add_assoc] using
    (COps.dimensionShiftingIso hY hYacyclic n hn ≪≫
      (groupCohomology.functor k G (n + 1)).mapIso e ≪≫
      COps.dimensionShiftingIso hX hXacyclic (n + 1)
        (Nat.succ_pos n))

/-- Splicing two homological dimension shifts lowers degree by two.  This is
the part of Theorem II.3.11 representing Tate degrees at most `-4`. -/
noncomputable def homologyDoubleShift
    {X Y : ShortComplex (Rep.{u} k G)}
    (hX : X.ShortExact) (hY : Y.ShortExact)
    (e : Y.X₁ ≅ X.X₃)
    (hXacyclic : ∀ n : ℕ, 0 < n → IsZero (groupHomology X.X₂ n))
    (hYacyclic : ∀ n : ℕ, 0 < n → IsZero (groupHomology Y.X₂ n))
    (n : ℕ) (hn : 0 < n) :
    groupHomology Y.X₃ (n + 2) ≅ groupHomology X.X₁ n := by
  simpa [Nat.add_assoc] using
    (homologyShiftingIso hY hYacyclic (n + 1) (Nat.succ_pos n) ≪≫
      (groupHomology.functor k G (n + 1)).mapIso e ≪≫
      homologyShiftingIso hX hXacyclic n hn)

end

end Submission.CField.Shifting

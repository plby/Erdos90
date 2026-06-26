import Submission.ClassField.Shifting.DoubleShift
import Submission.ClassField.Shifting.TateZero
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Milne, Class Field Theory, Theorem II.3.11: exceptional degrees

For trivial integral coefficients, Tate degree zero is cyclic of order
`|G|`, while Tate degree minus one vanishes.  These are the two exceptional
inputs in the two-degree shift.
-/

namespace Submission.CField.Shifting

open AddSubgroup CategoryTheory.Limits Representation

noncomputable section

variable (G : Type) [Group G] [Fintype G]

/-- The norm on trivial integral coefficients is injective, since it is
multiplication by the nonzero integer `|G|`. -/
private theorem coinvariants_invariants_injective :
    Function.Injective
      (normCoinvariantsInvariants (Rep.trivial ℤ G ℤ)) := by
  intro x y hxy
  induction x using Coinvariants.induction_on with
  | _ x =>
      induction y using Coinvariants.induction_on with
      | _ y =>
          have h := congrArg Subtype.val hxy
          change (Rep.trivial ℤ G ℤ).ρ.norm x =
            (Rep.trivial ℤ G ℤ).ρ.norm y at h
          have hmul : (Fintype.card G : ℤ) * x =
              (Fintype.card G : ℤ) * y := by
            simpa [Representation.norm, nsmul_eq_mul] using h
          have hcard : (Fintype.card G : ℤ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          have hxy' : x = y := mul_left_cancel₀ hcard hmul
          exact congrArg (Coinvariants.mk (Rep.trivial ℤ G ℤ).ρ) hxy'

/-- Tate degree minus one of the trivial integral module is zero. -/
theorem subsingleton_trivial_int :
    Subsingleton (tateCohomologyOne (Rep.trivial ℤ G ℤ)) := by
  constructor
  intro x y
  apply Subtype.ext
  apply coinvariants_invariants_injective G
  rw [LinearMap.mem_ker.mp x.property, LinearMap.mem_ker.mp y.property]

/-- The degree-zero part of Theorem II.3.11, determined by the chosen
generator of `H²(G,C)`. -/
noncomputable def tateZeroGenerator
    (C : Rep ℤ G) (gamma : groupCohomology C 2)
    (hgamma : ∀ x : groupCohomology C 2, x ∈ zmultiples gamma)
    (hcard : Nat.card (groupCohomology C 2) = Fintype.card G) :
    tateCohomologyZero (Rep.trivial ℤ G ℤ) ≃ₗ[ℤ]
      groupCohomology C 2 :=
  ((tateCohomologyTrivial G).trans
    (zmodAddEquivOfGenerator hgamma hcard)).toIntLinearEquiv

/-- The degree-minus-one part of Theorem II.3.11.  Both sides vanish under
Milne's `H¹` hypothesis. -/
noncomputable def tateNegEquiv
    (C : Rep ℤ G) (hC1 : IsZero (groupCohomology C 1)) :
    tateCohomologyOne (Rep.trivial ℤ G ℤ) ≃ₗ[ℤ]
      groupCohomology C 1 := by
  letI : Subsingleton
      (tateCohomologyOne (Rep.trivial ℤ G ℤ)) :=
    subsingleton_trivial_int G
  letI : Subsingleton (groupCohomology C 1) :=
    ModuleCat.subsingleton_of_isZero hC1
  exact LinearEquiv.ofSubsingleton _ _

end

end Submission.CField.Shifting

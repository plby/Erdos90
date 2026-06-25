import Submission.ClassField.RayClassGroups.Modulus
import Submission.ClassField.Examples.RayResidueMap

/-!
# Chapter V, Section 1, Example 1.4

For the rational modulus `2^3 * 17^2 * 19 * infinity`, the finite part is the
integer `43928`.  The positive fractions prime to this integer map to its
residue-class units, and the kernel condition is exactly congruence of the
numerator and denominator modulo `43928`.
-/

namespace Submission.CField.RCGroups

open Submission.CField.Examples

/-- The finite part of Milne's explicit modulus
`(2)^3 * (17)^2 * (19) * infinity`. -/
def finiteModulus : ℕ := 2 ^ 3 * 17 ^ 2 * 19

@[simp]
theorem finiteModulus_eq : finiteModulus = 43928 := by
  norm_num [finiteModulus]

theorem finiteModulus_pos : 0 < finiteModulus := by
  norm_num [finiteModulus]

/-- The residue map for the finite part of Example 1.4. -/
noncomputable def residueHom :
    PositiveCoprimeFraction finiteModulus →*
      (ZMod finiteModulus)ˣ :=
  positiveCoprimeHom finiteModulus

/-- The three finite congruence conditions in Example 1.4 combine into one
congruence modulo `2^3 * 17^2 * 19`. -/
theorem residue_hom_fraction (r s : ℕ)
    (hr : 0 < r ∧ r.Coprime finiteModulus)
    (hs : 0 < s ∧ s.Coprime finiteModulus) :
    residueHom
        (positiveCoprimeFraction finiteModulus r s hr hs) = 1 ↔
      r ≡ s [MOD finiteModulus] := by
  exact positive_coprime_fraction
    finiteModulus r s hr hs

/-- The ray residue map in Example 1.4 is onto. -/
theorem residueHom_surjective :
    Function.Surjective residueHom :=
  positive_coprime_surjective finiteModulus_pos

/-- The elementary rational ray quotient for Example 1.4. -/
noncomputable def rayQuotientEquiv :
    PositiveCoprimeFraction finiteModulus ⧸ residueHom.ker ≃*
      (ZMod finiteModulus)ˣ :=
  coprimeFractionEquiv finiteModulus_pos

end Submission.CField.RCGroups

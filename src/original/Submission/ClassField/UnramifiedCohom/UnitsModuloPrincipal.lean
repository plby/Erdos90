import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Submission.Group.Edmonton.HallCommutatorIdentities

/-!
# Milne, Class Field Theory, Lemma III.1.3: units modulo principal units

For a commutative local ring, reduction modulo the maximal ideal identifies
the unit group modulo `1 + 𝔪` with the unit group of the residue field.
-/

namespace Submission.CField.UCohom

open IsLocalRing

noncomputable section

variable (R : Type*) [CommRing R] [IsLocalRing R]

private abbrev residueUnits : Rˣ →* (ResidueField R)ˣ :=
  Units.map (residue R).toMonoidHom

private theorem ker_residueUnits :
    (residueUnits R).ker =
      Edmonton.idealUnitSubgroup (maximalIdeal R) 1 := by
  ext u
  rw [MonoidHom.mem_ker]
  simp only [residueUnits, Units.ext_iff, Edmonton.idealUnitSubgroup]
  change residue R (u : R) = 1 ↔ (u : R) - 1 ∈ maximalIdeal R ^ 1
  rw [← map_one (residue R), ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
  simp

/-- **Lemma III.1.3, first isomorphism.** Reduction modulo the maximal ideal
identifies the units modulo the first principal-unit subgroup with the units
of the residue field. -/
noncomputable def unitsPrincipalEquiv :
    Rˣ ⧸ Edmonton.idealUnitSubgroup (maximalIdeal R) 1 ≃*
      (ResidueField R)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (ker_residueUnits R).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (residueUnits R)
      (surjective_units_map_of_local_ringHom
        (residue R) residue_surjective inferInstance))

end

end Submission.CField.UCohom

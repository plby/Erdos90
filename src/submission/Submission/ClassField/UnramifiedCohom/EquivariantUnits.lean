import Mathlib.Algebra.Group.Action.Units
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Submission.ClassField.UnramifiedCohom.UnitsModuloPrincipal

/-!
# Milne, Class Field Theory, Lemma III.1.3: equivariance on units

Reduction modulo the maximal ideal identifies the first principal-unit
quotient with the units of the residue field *as a `G`-module*.  This file
upgrades the abstract group isomorphism in `Lemma13Units` to an isomorphism
of integral representations for every action on the local ring by ring
automorphisms.
-/

namespace Submission.CField.UCohom

open IsLocalRing

noncomputable section

universe u v

variable (G : Type u) [Group G]
variable (R : Type v) [CommRing R] [IsLocalRing R] [MulSemiringAction G R]

local instance : MulDistribMulAction G Rˣ :=
  Units.mulDistribMulActionRight

local instance : MulDistribMulAction G (ResidueField R)ˣ :=
  Units.mulDistribMulActionRight

private abbrev firstPrincipalUnits : Subgroup Rˣ :=
  Edmonton.idealUnitSubgroup (maximalIdeal R) 1

/-- Powers of the maximal ideal of a local ring are stable under every
action by ring automorphisms. -/
theorem smul_maximal_pow (g : G) (m : ℕ) {x : R}
    (hx : x ∈ maximalIdeal R ^ m) :
    g • x ∈ maximalIdeal R ^ m := by
  let e : R ≃+* R := MulSemiringAction.toRingEquiv G R g
  have he : (maximalIdeal R).map e = maximalIdeal R :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  have hep : (maximalIdeal R ^ m).map e = maximalIdeal R ^ m := by
    rw [Ideal.map_pow, he]
  rw [← hep]
  exact Ideal.mem_map_of_mem e hx

/-- The natural action on units preserves the first principal-unit
subgroup, hence descends to its quotient. -/
@[implicit_reducible]
private noncomputable def firstPrincipalAction :
    MulAction.QuotientAction G (firstPrincipalUnits R) where
  inv_mul_mem g x y hxy := by
    change (((g • x)⁻¹ * (g • y) : Rˣ) : R) - 1 ∈ maximalIdeal R ^ 1
    have hxy' : (((x⁻¹ * y : Rˣ) : R) - 1) ∈ maximalIdeal R ^ 1 := hxy
    have hs := smul_maximal_pow G R g 1 hxy'
    have hs' : (((g • (x⁻¹ * y) : Rˣ) : R) - 1) ∈
        maximalIdeal R ^ 1 := by
      simpa only [Units.coe_smul, smul_sub, smul_one] using hs
    simpa only [smul_mul', smul_inv] using hs'

/-- The descended action on the quotient acts by group automorphisms. -/
@[implicit_reducible]
private noncomputable def mulDistribAction :
    letI : MulAction.QuotientAction G (firstPrincipalUnits R) :=
      firstPrincipalAction G R
    MulDistribMulAction G (Rˣ ⧸ firstPrincipalUnits R) := by
  letI : MulAction.QuotientAction G (firstPrincipalUnits R) :=
    firstPrincipalAction G R
  letI : MulAction G (Rˣ ⧸ firstPrincipalUnits R) := inferInstance
  exact
    { smul_mul := by
        intro g x y
        induction x using QuotientGroup.induction_on with
        | _ x =>
          induction y using QuotientGroup.induction_on with
          | _ y =>
            simp only [← QuotientGroup.mk_mul, MulAction.Quotient.smul_mk,
              smul_mul']
      smul_one := by
        intro g
        rw [← QuotientGroup.mk_one, MulAction.Quotient.smul_mk, smul_one] }

/-- **Lemma III.1.3, first displayed isomorphism, equivariant form.**
Reduction identifies `Rˣ / (1 + 𝔪)` with the units of the residue field as
integral `G`-representations. -/
noncomputable def gModuleIso :
    letI : MulAction.QuotientAction G (firstPrincipalUnits R) :=
      firstPrincipalAction G R
    letI : MulDistribMulAction G (Rˣ ⧸ firstPrincipalUnits R) :=
      mulDistribAction G R
    Rep.ofMulDistribMulAction G (Rˣ ⧸ firstPrincipalUnits R) ≅
      Rep.ofMulDistribMulAction G (ResidueField R)ˣ := by
  letI : MulAction.QuotientAction G (firstPrincipalUnits R) :=
    firstPrincipalAction G R
  letI : MulDistribMulAction G (Rˣ ⧸ firstPrincipalUnits R) :=
    mulDistribAction G R
  let e := unitsPrincipalEquiv R
  let eAdd : Additive (Rˣ ⧸ firstPrincipalUnits R) ≃+
      Additive (ResidueField R)ˣ := e.toAdditive
  let eRep :
      (Rep.ofMulDistribMulAction G (Rˣ ⧸ firstPrincipalUnits R)).ρ.Equiv
        (Rep.ofMulDistribMulAction G (ResidueField R)ˣ).ρ :=
    Representation.Equiv.mk eAdd.toIntLinearEquiv (by
      intro g
      apply LinearMap.ext
      rintro (q : Additive (Rˣ ⧸ firstPrincipalUnits R))
      apply Additive.toMul.injective
      change e (g • (q.toMul : Rˣ ⧸ firstPrincipalUnits R)) =
        g • e (q.toMul : Rˣ ⧸ firstPrincipalUnits R)
      induction q.toMul using QuotientGroup.induction_on with
      | _ u =>
        change e (QuotientGroup.mk (g • u)) = g • e (QuotientGroup.mk u)
        apply Units.ext
        exact IsLocalRing.ResidueField.residue_smul G g (u : R))
  exact Rep.mkIso eRep

end

end Submission.CField.UCohom

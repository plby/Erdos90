import Submission.ClassField.Shifting.BarProjection
import Submission.ClassField.ArtinReciprocity.Verlagerung

/-!
# Quotient-out formula for the transfer

This identifies the group-theoretic transfer with the product of the same
right-coset correction terms used by the explicit bar-resolution projection.
-/

open scoped Pointwise

namespace Submission.CField.Shifting

open MulAction Subgroup Subgroup.leftTransversals

variable {G : Type*} [Group G]

noncomputable def inverseOutRep (H : Subgroup G)
    (q : Quotient (QuotientGroup.leftRel H)) : G :=
  (Quotient.out
    ((QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm q))⁻¹

theorem inverse_out_rep (H : Subgroup G)
    (q : Quotient (QuotientGroup.leftRel H)) :
    (Quotient.mk'' (inverseOutRep H q) :
      Quotient (QuotientGroup.leftRel H)) = q := by
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  change Quotient.mk'' ((Quotient.out (e.symm q))⁻¹) = q
  calc
    _ = e (e.symm q) := by
      change e (Quotient.mk (QuotientGroup.rightRel H)
        (Quotient.out (e.symm q))) = e (e.symm q)
      exact congrArg e (Quotient.out_eq _)
    _ = q := e.apply_symm_apply q

noncomputable def inverseOutTransversal (H : Subgroup G) : H.LeftTransversal :=
  ⟨Set.range (inverseOutRep H), isComplement_range_left (inverse_out_rep H)⟩

theorem inverse_out_transversal (H : Subgroup G)
    (q : Quotient (QuotientGroup.leftRel H)) :
    ((inverseOutTransversal H).2.leftQuotientEquiv q : G) = inverseOutRep H q := by
  exact IsComplement.leftQuotientEquiv_apply (inverse_out_rep H) q

theorem right_mk_mul (H : Subgroup G) (x g : G) :
    QuotientGroup.quotientRightRelEquivQuotientLeftRel H
        (Quotient.mk (QuotientGroup.rightRel H) (x * g)) =
      (g⁻¹ • QuotientGroup.quotientRightRelEquivQuotientLeftRel H
        (Quotient.mk (QuotientGroup.rightRel H) x) :
          Quotient (QuotientGroup.leftRel H)) := by
  change Quotient.mk'' ((x * g)⁻¹) = Quotient.mk'' (g⁻¹ * x⁻¹)
  rw [mul_inv_rev]

theorem right_out_mul (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) (g : G) :
    QuotientGroup.quotientRightRelEquivQuotientLeftRel H
        (Quotient.mk (QuotientGroup.rightRel H) (q.out * g)) =
      (g⁻¹ • QuotientGroup.quotientRightRelEquivQuotientLeftRel H q :
        Quotient (QuotientGroup.leftRel H)) := by
  rw [right_mk_mul]
  exact congrArg (g⁻¹ • ·)
    (congrArg (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)
      (Quotient.out_eq q))

theorem out_rep_equiv (H : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel H)) :
    inverseOutRep H
        (QuotientGroup.quotientRightRelEquivQuotientLeftRel H q) = q.out⁻¹ := by
  simp [inverseOutRep]

theorem smul_out_transversal (H : Subgroup G) (g : G)
    (q : Quotient (QuotientGroup.rightRel H)) :
    (((g • inverseOutTransversal H).2.leftQuotientEquiv
        (QuotientGroup.quotientRightRelEquivQuotientLeftRel H q) : G)) =
      g * (Quotient.out
        (Quotient.mk (QuotientGroup.rightRel H) (q.out * g)))⁻¹ := by
  rw [smul_apply_eq_smul_apply_inv_smul]
  change g * ((inverseOutTransversal H).2.leftQuotientEquiv
    (g⁻¹ • QuotientGroup.quotientRightRelEquivQuotientLeftRel H q) : G) = _
  rw [← right_out_mul H q g]
  rw [inverse_out_transversal, out_rep_equiv]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem transfer_prod_coset
    (H : Subgroup G) [H.FiniteIndex] (g : G) :
    MonoidHom.transfer (Abelianization.of : H →* Abelianization H) g =
      ∏ q : Quotient (QuotientGroup.rightRel H),
        Abelianization.of (Rep.rightCosetCorrection H (q.out * g)) := by
  classical
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  letI : Fintype (Quotient (QuotientGroup.leftRel H)) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel H)) :=
    Fintype.ofEquiv (Quotient (QuotientGroup.leftRel H)) e.symm
  rw [MonoidHom.transfer_def (Abelianization.of : H →* Abelianization H)
    (inverseOutTransversal H)]
  unfold Subgroup.leftTransversals.diff
  symm
  apply Fintype.prod_equiv e
  intro q
  apply congrArg Abelianization.of
  apply Subtype.ext
  change
    (Rep.rightCosetCorrection H (q.out * g) : G) =
      (((inverseOutTransversal H).2.leftQuotientEquiv (e q) : G))⁻¹ *
        (((g • inverseOutTransversal H).2.leftQuotientEquiv (e q) : G))
  rw [inverse_out_transversal, out_rep_equiv]
  rw [smul_out_transversal]
  simp [Rep.rightCosetCorrection, Rep.rightCosetRep, mul_assoc]

theorem transfer_coset_correction
    (H : Subgroup G) [H.FiniteIndex] (g : G) :
    Additive.ofMul
        (MonoidHom.transfer (Abelianization.of : H →* Abelianization H) g) =
      ∑ q : Quotient (QuotientGroup.rightRel H),
        Additive.ofMul
          (Abelianization.of (Rep.rightCosetCorrection H (q.out * g))) := by
  classical
  let e := QuotientGroup.quotientRightRelEquivQuotientLeftRel H
  letI : Fintype (Quotient (QuotientGroup.leftRel H)) :=
    Subgroup.fintypeQuotientOfFiniteIndex
  letI : Fintype (Quotient (QuotientGroup.rightRel H)) :=
    Fintype.ofEquiv (Quotient (QuotientGroup.leftRel H)) e.symm
  rw [transfer_prod_coset]
  exact ofMul_prod _ _

end Submission.CField.Shifting

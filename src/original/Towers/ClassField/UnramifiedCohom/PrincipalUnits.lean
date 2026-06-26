import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic
import Towers.Group.Edmonton.HallCommutatorIdentities

/-!
# Milne, Class Field Theory, Lemma III.1.3: successive principal units

For a commutative local ring and a positive integer `m`, subtraction of one
identifies the quotient of the `m`th principal-unit subgroup by the next
subgroup with the additive quotient `mathfrak m^m / mathfrak m^(m+1)`.
-/

namespace Towers.CField.UCohom

open IsLocalRing

noncomputable section

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The copy of `I^(m+1)` inside the module `I^m`. -/
def idealSuccessiveDenominator (I : Ideal R) (m : Nat) :
    Submodule R (I ^ m : Ideal R) :=
  Submodule.comap
    ((I ^ m : Ideal R) : Submodule R R).subtype
    ((I ^ (m + 1) : Ideal R) : Submodule R R)

/-- The additive quotient `I^m / I^(m+1)`, with the denominator regarded as
a submodule of `I^m`. -/
abbrev IdealSuccessiveQuotient (I : Ideal R) (m : Nat) :=
  @HasQuotient.Quotient
    (↑(I ^ m))
    (Submodule R (↑(I ^ m)))
    Submodule.hasQuotient
    (idealSuccessiveDenominator R I m)

omit [IsLocalRing R] in
lemma successive_denominator_top (I : Ideal R) (m : Nat) :
    idealSuccessiveDenominator R I m = I • ⊤ := by
  ext x
  simp [idealSuccessiveDenominator, Submodule.mem_smul_top_iff, pow_succ']

/-- For a nonzero principal ideal, its successive power quotient is the
additive group of the residue ring. -/
noncomputable def idealSuccessiveEquiv [IsDomain R]
    (I : Ideal R) (hI : I.IsPrincipal) (hI0 : I ≠ ⊥) (m : Nat) :
    IdealSuccessiveQuotient R I m ≃+ (R ⧸ I) :=
  LinearEquiv.toAddEquiv <|
    (Submodule.quotEquivOfEq
      (idealSuccessiveDenominator R I m) (I • ⊤)
      (successive_denominator_top R I m)).trans
        (Ideal.quotEquivPowQuotPowSucc hI hI0 m).symm

private abbrev principalUnits (m : Nat) : Subgroup Rˣ :=
  Edmonton.idealUnitSubgroup (maximalIdeal R) m

private abbrev successiveIdealPower (m : Nat) : Type _ :=
  IdealSuccessiveQuotient R (maximalIdeal R) m

/-- The map on the `m`th principal-unit subgroup induced by `u ↦ u - 1`.
The product correction `(u - 1)(v - 1)` lies in `mathfrak m^(m+1)` when
`m > 0`. -/
private def principalSuccessiveHom (m : Nat) (hm : 0 < m) :
    principalUnits (R := R) m →*
      Multiplicative (successiveIdealPower (R := R) m) where
  toFun u := Multiplicative.ofAdd <|
    Submodule.Quotient.mk
      (show ↑((maximalIdeal R) ^ m) from
        ⟨(u.1 : R) - 1, u.2⟩)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change Submodule.Quotient.mk
        (show ↑((maximalIdeal R) ^ m) from ⟨(1 : R) - 1, by simp⟩) = 0
    rw [show
      (show ↑((maximalIdeal R) ^ m) from ⟨(1 : R) - 1, by simp⟩) = 0 by
        apply Subtype.ext
        simp]
    rfl
  map_mul' := by
    intro u v
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd, toAdd_mul]
    change Submodule.Quotient.mk
        (show ↑((maximalIdeal R) ^ m) from
          ⟨((u * v).1 : R) - 1, (u * v).2⟩) =
      Submodule.Quotient.mk
          (show ↑((maximalIdeal R) ^ m) from ⟨(u.1 : R) - 1, u.2⟩) +
        Submodule.Quotient.mk
          (show ↑((maximalIdeal R) ^ m) from ⟨(v.1 : R) - 1, v.2⟩)
    rw [← Submodule.Quotient.mk_add]
    apply (Submodule.Quotient.eq _).2
    change
      (((u.1 : R) * (v.1 : R) - 1) -
          (((u.1 : R) - 1) + ((v.1 : R) - 1))) ∈
        (maximalIdeal R) ^ (m + 1)
    rw [show
        ((u.1 : R) * (v.1 : R) - 1) -
            (((u.1 : R) - 1) + ((v.1 : R) - 1)) =
          ((u.1 : R) - 1) * ((v.1 : R) - 1) by ring]
    apply Ideal.pow_le_pow_right (by omega : m + 1 ≤ m + m)
    exact Edmonton.ideal_pow_add (maximalIdeal R) u.2 v.2

private theorem principal_successive_surjective (m : Nat) (hm : 0 < m) :
    Function.Surjective (principalSuccessiveHom R m hm) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ a =>
      have haMaximal : (a : R) ∈ maximalIdeal R :=
        Ideal.pow_le_self hm.ne' a.2
      have hunit : IsUnit (1 + (a : R)) := by
        have hneg : -(a : R) ∈ nonunits R := by
          rw [← IsLocalRing.mem_maximalIdeal]
          exact (maximalIdeal R).neg_mem haMaximal
        simpa only [sub_neg_eq_add] using
          IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(a : R)) hneg
      let u : Rˣ := hunit.unit
      have hu : (u : R) = 1 + (a : R) := hunit.unit_spec
      have huPrincipal : u ∈ principalUnits (R := R) m := by
        change (u : R) - 1 ∈ (maximalIdeal R) ^ m
        rw [hu]
        rw [add_sub_cancel_left]
        exact a.2
      refine ⟨⟨u, huPrincipal⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      change Submodule.Quotient.mk
          (show ↑((maximalIdeal R) ^ m) from ⟨(u : R) - 1, huPrincipal⟩) =
        Submodule.Quotient.mk a
      apply congrArg Submodule.Quotient.mk
      apply Subtype.ext
      simp [hu]

private theorem ker_principal_successive (m : Nat) (hm : 0 < m) :
    (principalSuccessiveHom R m hm).ker =
      (principalUnits (R := R) (m + 1)).subgroupOf
        (principalUnits (R := R) m) := by
  ext u
  change Submodule.Quotient.mk
      (show ↑((maximalIdeal R) ^ m) from ⟨(u.1 : R) - 1, u.2⟩) = 0 ↔
    (u.1 : R) - 1 ∈ (maximalIdeal R) ^ (m + 1)
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/-- **Lemma III.1.3, second isomorphism.** For `m > 0`, subtraction of one
identifies successive principal units with the corresponding additive ideal
quotient. The codomain is written multiplicatively only so that this is a
group isomorphism. -/
noncomputable def principalSuccessiveEquiv (m : Nat) (hm : 0 < m) :
    principalUnits (R := R) m ⧸
        (principalUnits (R := R) (m + 1)).subgroupOf
          (principalUnits (R := R) m) ≃*
      Multiplicative (IdealSuccessiveQuotient R (maximalIdeal R) m) :=
  (QuotientGroup.quotientMulEquivOfEq
      (ker_principal_successive R m hm).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (principalSuccessiveHom R m hm)
      (principal_successive_surjective R m hm))

/-- **Lemma III.1.3, second displayed isomorphism.** If the maximal ideal is
nonzero and principal (in particular for a nontrivial discrete valuation
ring), every successive principal-unit quotient is the additive group of the
residue field. -/
noncomputable def principalSuccessiveResidue [IsDomain R]
    (hprincipal : (maximalIdeal R).IsPrincipal)
    (hne : maximalIdeal R ≠ ⊥) (m : Nat) (hm : 0 < m) :
    principalUnits (R := R) m ⧸
        (principalUnits (R := R) (m + 1)).subgroupOf
          (principalUnits (R := R) m) ≃*
      Multiplicative (ResidueField R) :=
  (principalSuccessiveEquiv R m hm).trans <|
    AddEquiv.toMultiplicative <|
      idealSuccessiveEquiv R (maximalIdeal R)
        hprincipal hne m

@[simp]
theorem principal_successive_mk (m : Nat) (hm : 0 < m)
    (u : principalUnits (R := R) m) :
    principalSuccessiveEquiv R m hm (QuotientGroup.mk u) =
      Multiplicative.ofAdd
        (Submodule.Quotient.mk
          (show ↑((maximalIdeal R) ^ m) from ⟨(u.1 : R) - 1, u.2⟩)) :=
  rfl

end

end Towers.CField.UCohom

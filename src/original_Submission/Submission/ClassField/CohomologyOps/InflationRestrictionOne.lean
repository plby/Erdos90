import Submission.ClassField.CohomologyOps.DimensionShiftingIso

/-!
# Milne, Class Field Theory, Proposition II.1.34

This file begins the inflation-restriction sequence with the degree-one case
and the representation-theoretic compatibility needed for Milne's
dimension-shifting proof in higher degrees.
-/

namespace Submission.CField.COps

open CategoryTheory Rep

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G]

section DegreeOne

variable (A : Rep k G) (H : Subgroup G) [H.Normal]

/-- The degree-one inflation-restriction complex from Proposition II.1.34. -/
noncomputable abbrev inflationRestrictionOne : ShortComplex (ModuleCat k) :=
  groupCohomology.H1InfRes A H

/-- Inflation is injective in degree one. -/
instance inflation_restriction_mono : Mono (inflationRestrictionOne A H).f :=
  inferInstance

/-- **Proposition II.1.34, degree one.** The sequence
`0 -> H^1(G/H, A^H) -> H^1(G, A) -> H^1(H, A)` is exact. -/
theorem inflation_restriction_exact : (inflationRestrictionOne A H).Exact :=
  groupCohomology.H1InfRes_exact A H

end DegreeOne

section DimensionShiftMiddle

variable (A : Rep k G) (H : Subgroup G) [H.Normal]

private abbrev middle := (dimensionShiftSequence A).X₂

/-- An `H`-invariant function on `G` descends to a function on `G/H`.
This is the coefficient isomorphism used in the dimension-shifting proof of
inflation-restriction. -/
noncomputable def shiftMiddleIso :
    (middle A).quotientToInvariants H ≅
      Rep.coind (⊥ : Subgroup (G ⧸ H)).subtype
        (Rep.trivial k (⊥ : Subgroup (G ⧸ H)) A) := by
  let e : ((middle A).quotientToInvariants H) ≃ₗ[k]
      Rep.coind (⊥ : Subgroup (G ⧸ H)).subtype
        (Rep.trivial k (⊥ : Subgroup (G ⧸ H)) A) :=
    { toFun := fun f =>
        ⟨fun q => Quotient.liftOn' q (fun g => f.1.1 g) (by
            intro g h hgh
            have hs : g⁻¹ * h ∈ H := QuotientGroup.leftRel_apply.1 hgh
            have hfixed := f.2 ⟨g⁻¹ * h, hs⟩
            have happ := congrArg
              (fun x : middle A => x.1 g) hfixed
            change f.1.1 (g * (g⁻¹ * h)) = f.1.1 g at happ
            simpa [mul_assoc] using happ.symm),
          by
            intro h q
            have hh : h = (1 : (⊥ : Subgroup (G ⧸ H))) :=
              Subtype.ext (Subgroup.mem_bot.mp h.2)
            subst hh
            simp⟩
      invFun := fun f =>
        ⟨⟨fun g => f.1 (QuotientGroup.mk' H g), by
            intro h g
            have hh : h = (1 : (⊥ : Subgroup G)) :=
              Subtype.ext (Subgroup.mem_bot.mp h.2)
            subst hh
            simp⟩,
          fun h => by
            apply Subtype.ext
            funext g
            change f.1 (QuotientGroup.mk' H (g * h.1)) =
              f.1 (QuotientGroup.mk' H g)
            rw [map_mul]
            have hh : QuotientGroup.mk' H h.1 = 1 :=
              (QuotientGroup.eq_one_iff h.1).2 h.2
            rw [hh, mul_one]⟩
      left_inv := fun f => by
        apply Subtype.ext
        apply Subtype.ext
        ext g
        rfl
      right_inv := fun f => by
        apply Subtype.ext
        ext q
        induction q using QuotientGroup.induction_on with
        | H g => rfl
      map_add' := fun f g => by
        apply Subtype.ext
        ext q
        induction q using QuotientGroup.induction_on with
        | H x => rfl
      map_smul' := fun r f => by
        apply Subtype.ext
        ext q
        induction q using QuotientGroup.induction_on with
        | H x => rfl }
  exact Rep.mkIso {
    toLinearEquiv := e
    isIntertwining' := fun q => by
      induction q using QuotientGroup.induction_on with
      | H g =>
          apply LinearMap.ext
          intro f
          apply Subtype.ext
          ext x
          induction x using QuotientGroup.induction_on with
          | H x => rfl }

end DimensionShiftMiddle

end

end Submission.CField.COps

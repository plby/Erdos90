import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-!
# Hilbert 90 for subgroups of a Galois group

Mathlib proves Noether's Hilbert 90 for the full automorphism group.  Tate's
local reciprocity construction needs the same vanishing after restriction to
every subgroup.  The usual twisted-trace proof works verbatim for any finite
subgroup of field automorphisms, so we record it directly here.
-/

namespace Towers.CField.LRecip

open CategoryTheory groupCohomology

noncomputable section

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

attribute [local instance] Units.mulDistribMulActionRight

/-- The twisted trace attached to a cocycle on a subgroup of the Galois
group. -/
private noncomputable def hilbert90Aux
    (H : Subgroup Gal(L/K)) (f : H → Lˣ) : L → L :=
  Finsupp.linearCombination L (fun phi : H ↦ (phi.1 : L → L))
    (Finsupp.equivFunOnFinite.symm (fun phi ↦ (f phi : L)))

private theorem hilbert_90_aux
    (H : Subgroup Gal(L/K)) (f : H → Lˣ) :
    hilbert90Aux H f ≠ 0 := by
  have hlin : LinearIndependent L (fun phi : H ↦ (phi.1 : L → L)) :=
    LinearIndependent.comp
      (linearIndependent_monoidHom L L)
      (fun phi : H ↦ phi.1)
      (fun x y h ↦ by
        apply Subtype.ext
        apply AlgEquiv.ext
        intro z
        exact congrArg (fun q : L →* L ↦ q z) h)
  have h := linearIndependent_iff.1 hlin
    (Finsupp.equivFunOnFinite.symm (fun phi ↦ (f phi : L)))
  intro hzero
  exact Units.ne_zero (f 1)
    (DFunLike.ext_iff.1 (h hzero) 1)

/-- Noether's cocycle form of Hilbert 90 for a finite subgroup of
`Gal(L/K)`. -/
theorem coboundary_galois_subgroup
    (H : Subgroup Gal(L/K)) (f : H → Lˣ) (hf : IsMulCocycle₁ f) :
    IsMulCoboundary₁ f := by
  letI : Fintype H := Fintype.ofFinite H
  obtain ⟨z, hz⟩ : ∃ z, hilbert90Aux H f z ≠ 0 :=
    not_forall.1 (fun h ↦ hilbert_90_aux H f (funext h))
  have hsum : hilbert90Aux H f z = ∑ h, f h * h.1 z := by
    simp [hilbert90Aux, Finsupp.linearCombination,
      Finsupp.sum_fintype]
  use (Units.mk0 (hilbert90Aux H f z) hz)⁻¹
  intro g
  simp only [IsMulCocycle₁, Subgroup.smul_def, AlgEquiv.smul_units_def,
    map_inv, div_inv_eq_mul, inv_mul_eq_iff_eq_mul, Units.ext_iff, hsum,
    Units.val_mul, Units.coe_map, Units.val_mk0, MonoidHom.coe_coe] at hf ⊢
  simp_rw [map_sum, map_mul, Finset.sum_mul, mul_assoc,
    mul_comm _ (f _ : L), ← mul_assoc, ← hf g]
  exact eq_comm.1 (Fintype.sum_bijective (fun i ↦ g * i)
    (Group.mulLeft_bijective g) _ _ (fun i ↦ rfl))

/-- **Subgroupwise Hilbert 90.** The first cohomology of the restriction of
the multiplicative Galois module to any subgroup is trivial. -/
theorem subgroup_hilbert90
    (H : Subgroup Gal(L/K)) :
    ∀ x : H1 (Rep.ofMulDistribMulAction H Lˣ), x = 0 := by
  intro a
  exact H1_induction_on a fun x ↦ (H1π_eq_zero_iff _).2 <| by
    refine (coboundariesOfIsMulCoboundary₁ ?_).2
    exact coboundary_galois_subgroup H
      (Additive.toMul ∘ x)
      (isMulCocycle₁_of_mem_cocycles₁ _ x.2)

/-- Categorical form of subgroupwise Hilbert 90, ready for Tate's theorem. -/
theorem hilbert_90_zero
    (H : Subgroup Gal(L/K)) :
    CategoryTheory.Limits.IsZero
      (groupCohomology
        (Rep.res H.subtype
          (Rep.ofMulDistribMulAction Gal(L/K) Lˣ)) 1) := by
  change CategoryTheory.Limits.IsZero
    (groupCohomology (Rep.ofMulDistribMulAction H Lˣ) 1)
  letI : Subsingleton
      (H1 (Rep.ofMulDistribMulAction H Lˣ)) :=
    ⟨fun x y ↦ (subgroup_hilbert90 H x).trans
      (subgroup_hilbert90 H y).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

end

end Towers.CField.LRecip

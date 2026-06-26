import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Chapter II, Remark 1.21: the connecting cocycle

For a short exact sequence of `G`-modules, lift a cocycle to a cochain in the
middle module.  Its differential lands in the submodule and represents the
image under the connecting homomorphism.
-/

namespace Submission.CField.COps

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]

noncomputable section

/-- **Remark II.1.21.** If `phi` is a cocycle, `phiTilde` is a cochain lift,
and `dPhiTilde` is the unique cochain in the left module whose image is the
differential of that lift, then `dPhiTilde` represents the connecting class.
-/
theorem connecting_hom_lift
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    {r s : ℕ} (hrs : r + 1 = s)
    (phi : (Fin r → G) → X.X₃)
    (hphi : (inhomogeneousCochains X.X₃).d r s phi = 0)
    (phiTilde : (Fin r → G) → X.X₂)
    (hlift : (cochainsMap (MonoidHom.id G) X.g).f r phiTilde = phi)
    (dPhiTilde : (Fin s → G) → X.X₁)
    (hfactor : X.f.hom ∘ dPhiTilde =
      (inhomogeneousCochains X.X₂).d r s phiTilde) :
    δ hX r s hrs
        (π X.X₃ r (cocyclesMk phi (by subst hrs; simpa using hphi))) =
      π X.X₁ s (cocyclesMkOfCompEqD hX hfactor) := by
  exact δ_apply hX hrs phi hphi phiTilde hlift dPhiTilde hfactor

/-- **Remark II.1.21, unconditional construction.** Short exactness supplies
both the cochain lift and the factorization of its differential through the
left module; that factor is the cocycle representing the connecting class. -/
theorem lift_representing_connecting
    {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    {r s : ℕ} (hrs : r + 1 = s)
    (phi : (Fin r → G) → X.X₃)
    (hphi : (inhomogeneousCochains X.X₃).d r s phi = 0) :
    ∃ (phiTilde : (Fin r → G) → X.X₂)
      (dPhiTilde : (Fin s → G) → X.X₁),
      (cochainsMap (MonoidHom.id G) X.g).f r phiTilde = phi ∧
        ∃ hfactor : X.f.hom ∘ dPhiTilde =
          (inhomogeneousCochains X.X₂).d r s phiTilde,
        δ hX r s hrs
            (π X.X₃ r (cocyclesMk phi (by subst hrs; simpa using hphi))) =
          π X.X₁ s (cocyclesMkOfCompEqD hX hfactor) := by
  let Y := X.map (cochainsFunctor k G)
  have hY : Y.ShortExact := map_cochainsFunctor_shortExact hX
  have hYr : (Y.map (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) r)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact Y).mp hY r
  obtain ⟨phiTilde, hlift⟩ := hYr.moduleCat_surjective_g phi
  have hliftY : Y.g.f r phiTilde = phi := by
    exact hlift
  have hlift' : (cochainsMap (MonoidHom.id G) X.g).f r phiTilde = phi := by
    exact hlift
  let dPhiTildeInMiddle := (inhomogeneousCochains X.X₂).d r s phiTilde
  have hd_mem_ker : (Y.g.f s) dPhiTildeInMiddle = 0 := by
    calc
      (Y.g.f s) dPhiTildeInMiddle =
          (inhomogeneousCochains X.X₃).d r s (Y.g.f r phiTilde) := by
        have hcomm := Y.g.comm r s
        exact congrArg (fun q => q phiTilde) hcomm.symm
      _ = (inhomogeneousCochains X.X₃).d r s phi := by rw [hliftY]
      _ = 0 := hphi
  have hYs : (Y.map (HomologicalComplex.eval (ModuleCat k) (ComplexShape.up ℕ) s)).ShortExact :=
    (HomologicalComplex.shortExact_iff_degreewise_shortExact Y).mp hY s
  have hExact := hYs.exact
  rw [ShortComplex.moduleCat_exact_iff] at hExact
  obtain ⟨dPhiTilde, hfactor⟩ := hExact dPhiTildeInMiddle hd_mem_ker
  have hfactor' : X.f.hom ∘ dPhiTilde =
      (inhomogeneousCochains X.X₂).d r s phiTilde := by
    exact hfactor
  refine ⟨phiTilde, dPhiTilde, hlift', hfactor', ?_⟩
  exact connecting_hom_lift hX hrs phi hphi phiTilde hlift'
    dPhiTilde hfactor'

end

end Submission.CField.COps

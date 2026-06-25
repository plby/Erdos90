import Towers.NumberTheory.Galois.ResolventGaloisGroup
import Towers.NumberTheory.Galois.ResolventCoefficientDescent


/-!
# Descent of the Galois resolvent factor

For a Galois-equivariant labelling of roots, the Galois action on the
coefficients of the labelled linear form is the inverse of its permutation
action on the variables.  Consequently the orbit factor is coefficientwise
fixed and descends to the base field.
-/

namespace Towers.NumberTheory.Milne

open Equiv MulAction Polynomial
open scoped BigOperators

noncomputable section

variable {A K L ι : Type*} [Group A] [Finite A]
  [Field K] [Field L] [Algebra K L]
  [MulSemiringAction A L] [IsGaloisGroup A K L]
  [Fintype ι]

omit [Finite A] in
/-- Acting on the coefficients of the labelled linear form is the same as
acting on its variables by the inverse root permutation. -/
theorem resolvent_form_smul
    (rho : A →* Equiv.Perm ι) (alpha : ι → L)
    (halpha : ∀ a i, a • alpha i = alpha (rho a i)) (a : A) :
    MvPolynomial.map (MulSemiringAction.toRingHom A L a)
        (resolventLinearForm alpha) =
      (rho a)⁻¹ • resolventLinearForm alpha := by
  rw [smul_resolvent_form]
  simp only [resolventLinearForm, map_sum, map_mul, MvPolynomial.map_C,
    MulSemiringAction.toRingHom_apply,
    halpha, MvPolynomial.map_X, Function.comp_apply]
  rw [show ((rho a)⁻¹).symm = rho a by
    rw [Equiv.Perm.inv_def, Equiv.symm_symm]]

omit [Finite A] in
/-- The subgroup orbit factor is fixed by the coefficientwise Galois action. -/
theorem galois_resolvent_self
    (rho : A →* Equiv.Perm ι) (alpha : ι → L)
    (halpha : ∀ a i, a • alpha i = alpha (rho a i)) (a : A) :
    (galoisResolventFactor rho.range (resolventLinearForm alpha)).map
        (MvPolynomial.map (MulSemiringAction.toRingHom A L a)) =
      galoisResolventFactor rho.range (resolventLinearForm alpha) := by
  classical
  letI := Fintype.ofFinite (Equiv.Perm ι)
  let theta := resolventLinearForm alpha
  let ha : rho.range := ⟨(rho a)⁻¹, rho.range.inv_mem ⟨a, rfl⟩⟩
  change Polynomial.mapRingHom
      (MvPolynomial.map (MulSemiringAction.toRingHom A L a))
      (Finset.univ.prod fun h : rho.range => X - C (h.1 • theta)) =
    Finset.univ.prod fun h : rho.range => X - C (h.1 • theta)
  rw [map_prod]
  exact Fintype.prod_bijective (Equiv.mulRight ha) (Equiv.mulRight ha).bijective
    (fun h : rho.range =>
      (X - C (h.1 • theta)).map
        (MvPolynomial.map (MulSemiringAction.toRingHom A L a)))
    (fun h : rho.range => X - C (h.1 • theta)) (fun h => by
      simp only [Equiv.coe_mulRight]
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      congr 2
      change MvPolynomial.map (MulSemiringAction.toRingHom A L a)
          (MvPolynomial.rename h.1 theta) =
        MvPolynomial.rename (h.1 * (rho a)⁻¹) theta
      rw [MvPolynomial.map_rename,
        resolvent_form_smul rho alpha halpha a]
      exact (mul_smul h.1 (rho a)⁻¹ theta).symm)

omit [Finite A] in
/-- The factor containing the original labelled linear form descends from
`L[X,t]` to `K[X,t]`. -/
theorem descended_resolvent_factor
    (rho : A →* Equiv.Perm ι) (alpha : ι → L)
    (halpha : ∀ a i, a • alpha i = alpha (rho a i)) :
    ∃ F₀ : (MvPolynomial ι K)[X],
      F₀.map (MvPolynomial.map (algebraMap K L)) =
        galoisResolventFactor rho.range (resolventLinearForm alpha) := by
  apply mv_coefficientwise_fixed
    (G := A)
  exact galois_resolvent_self rho alpha halpha

section PolynomialGaloisGroup

variable {K : Type*} [Field K]

set_option maxHeartbeats 2000000 in
-- Unfolding both canonical splitting-field actions during the specialization
-- requires a larger elaboration budget.
/-- The descended form of Milne's Theorem 8.20 for the actual polynomial
Galois group.  After a harmless relabelling of the roots, the orbit factor
is defined over the base field, and its stabilizer is precisely the faithful
permutation image of `Polynomial.Gal p`.

The assertion that this descended orbit factor is irreducible is the
additional van der Waerden result cited (without proof) in Milne's proof. -/
theorem descended_resolvent_gal
    (p : K[X]) (hpsep : p.Separable) :
    let L := p.SplittingField
    let roots := p.rootSet L
    let rho : p.Gal →* Equiv.Perm roots :=
      @MulAction.toPermHom _ _ _
        (Polynomial.Gal.galActionAux (p := p))
    let alpha : roots → L := fun x => (x : L)
    ∃ F₀ : (MvPolynomial roots K)[X],
      F₀.map (MvPolynomial.map (algebraMap K L)) =
          galoisResolventFactor rho.range (resolventLinearForm alpha) ∧
      (F₀.map (MvPolynomial.map (algebraMap K L))) ∣
          fullResolventPolynomial (G := Equiv.Perm roots)
            (resolventLinearForm alpha) ∧
      stabilizer (Equiv.Perm roots)
          (F₀.map (MvPolynomial.map (algebraMap K L))) = rho.range ∧
      Nonempty
        (p.Gal ≃* stabilizer (Equiv.Perm roots)
          (F₀.map (MvPolynomial.map (algebraMap K L)))) := by
  let L := p.SplittingField
  let roots := p.rootSet L
  letI : IsGalois K L :=
    IsGalois.of_separable_splitting_field (p := p) hpsep
  letI : IsGaloisGroup p.Gal K L := IsGaloisGroup.of_isGalois K L
  letI : Fact ((p.map (algebraMap K L)).Splits) :=
    ⟨Polynomial.SplittingField.splits p⟩
  let rho : p.Gal →* Equiv.Perm roots :=
    @MulAction.toPermHom _ _ _
      (Polynomial.Gal.galActionAux (p := p))
  let alpha : roots → L := fun x => (x : L)
  have halpha : ∀ a i, a • alpha i = alpha (rho a i) := by
    intro a i
    rfl
  have hrhoInj : Function.Injective rho := by
    intro a b hab
    apply Polynomial.Gal.galActionHom_injective p L
    ext i
    let e := Polynomial.Gal.rootsEquivRoots p L
    change ((a • i : p.rootSet L) : L) = ((b • i : p.rootSet L) : L)
    rw [Polynomial.Gal.smul_def, Polynomial.Gal.smul_def]
    have hinner : rho a (e.symm i) = rho b (e.symm i) :=
      congrArg (fun sigma : Equiv.Perm roots => sigma (e.symm i)) hab
    have hout := congrArg (Polynomial.Gal.rootsEquivRoots p L) hinner
    exact congrArg Subtype.val hout
  obtain ⟨F₀, hF₀⟩ :=
    descended_resolvent_factor
      (A := p.Gal) (K := K) (L := L) rho alpha halpha
  have hstab : stabilizer (Equiv.Perm roots)
      (galoisResolventFactor rho.range (resolventLinearForm alpha)) =
        rho.range := by
    apply stabilizer_resolvent_factor
    rw [stabilizer_resolvent_bot alpha]
    · exact bot_le
    · exact Subtype.val_injective
  have hstabF₀ : stabilizer (Equiv.Perm roots)
      (F₀.map (MvPolynomial.map (algebraMap K L))) = rho.range := by
    rw [hF₀]
    exact hstab
  refine ⟨F₀, hF₀, ?_, ?_, ?_⟩
  · rw [hF₀]
    exact galois_resolvent_full rho.range _
  · rw [hF₀]
    exact hstab
  · let eRange : p.Gal ≃* rho.range :=
      MonoidHom.ofInjective hrhoInj
    exact ⟨eRange.trans (MulEquiv.subgroupCongr hstabF₀.symm)⟩

end PolynomialGaloisGroup

end

end Towers.NumberTheory.Milne

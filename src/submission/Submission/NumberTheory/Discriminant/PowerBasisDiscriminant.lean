import Mathlib

/-!
# Milne, Algebraic Number Theory, Proposition 2.34

The discriminant of a power basis is a squared Vandermonde product, equivalently a signed
norm of the derivative of the minimal polynomial.
-/

namespace Submission.NumberTheory.Milne

open Polynomial

/-- The Vandermonde-product formula in Proposition 2.34. -/
theorem discr_conjugate_differences
    (K L Ω : Type*) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsAlgClosed Ω]
    (pb : PowerBasis K L) (e : Fin pb.dim ≃ (L →ₐ[K] Ω)) :
    algebraMap K Ω (Algebra.discr K pb.basis) =
      ∏ i : Fin pb.dim, ∏ j ∈ Finset.Ioi i,
        (e j pb.gen - e i pb.gen) ^ 2 := by
  exact Algebra.discr_powerBasis_eq_prod K Ω pb e

/-- The signed-norm formula in Proposition 2.34. -/
theorem basis_discr_derivative
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) :
    Algebra.discr K pb.basis =
      (-1) ^ (Module.finrank K L * (Module.finrank K L - 1) / 2) *
        Algebra.norm K
          (Polynomial.aeval pb.gen (minpoly K pb.gen).derivative) := by
  exact Algebra.discr_powerBasis_eq_norm K pb

/-- Both descriptions of the power-basis discriminant from Proposition 2.34. -/
theorem basis_discriminant_formulas
    (K L Ω : Type*) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsAlgClosed Ω]
    (pb : PowerBasis K L) (e : Fin pb.dim ≃ (L →ₐ[K] Ω)) :
    algebraMap K Ω (Algebra.discr K pb.basis) =
        ∏ i : Fin pb.dim, ∏ j ∈ Finset.Ioi i,
          (e j pb.gen - e i pb.gen) ^ 2 ∧
      Algebra.discr K pb.basis =
        (-1) ^ (Module.finrank K L * (Module.finrank K L - 1) / 2) *
          Algebra.norm K
            (Polynomial.aeval pb.gen (minpoly K pb.gen).derivative) := by
  exact ⟨discr_conjugate_differences K L Ω pb e,
    basis_discr_derivative K L pb⟩

private theorem basis_aeval_aroots
    {K L E : Type*} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra K E] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [IsAlgClosed E]
    (pb : PowerBasis K L) (g : K[X]) :
    algebraMap K E (Algebra.norm K (Polynomial.aeval pb.gen g)) =
      (((minpoly K pb.gen).aroots E).map
        (fun x ↦ Polynomial.eval x (g.map (algebraMap K E)))).prod := by
  letI := Classical.decEq E
  letI : Fintype (L →ₐ[K] E) := minpoly.AlgHom.fintype K L E
  rw [Algebra.norm_eq_prod_embeddings K E]
  calc
    (∏ σ : L →ₐ[K] E, σ (Polynomial.aeval pb.gen g)) =
        ∏ x : {x // x ∈ (minpoly K pb.gen).aroots E},
          Polynomial.eval x.1 (g.map (algebraMap K E)) := by
      apply Fintype.prod_equiv pb.liftEquiv'
      intro σ
      rw [Polynomial.eval_map_algebraMap,
        PowerBasis.liftEquiv'_apply_coe, Polynomial.aeval_algHom_apply]
    _ = (((minpoly K pb.gen).aroots E).map
          (fun x ↦ Polynomial.eval x (g.map (algebraMap K E)))).prod := by
      rw [Finset.prod_mem_multiset]
      · rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
          Multiset.dedup_eq_self.mpr]
        exact nodup_roots
          (Separable.map (Algebra.IsSeparable.isSeparable K pb.gen))
      · intro x
        rfl

/-- The norm-resultant identity for a power basis. -/
theorem basis_aeval_resultant
    {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) (g : K[X]) :
    Algebra.norm K (Polynomial.aeval pb.gen g) =
      (minpoly K pb.gen).resultant g := by
  let E := AlgebraicClosure L
  let f := minpoly K pb.gen
  have hfmonic : f.Monic := minpoly.monic pb.isIntegral_gen
  apply (algebraMap K E).injective
  rw [basis_aeval_aroots pb g]
  rw [← Polynomial.resultant_map_map f g f.natDegree g.natDegree
    (algebraMap K E)]
  have hnatf : (f.map (algebraMap K E)).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective (algebraMap K E).injective f
  rw [← hnatf, Polynomial.resultant_eq_prod_eval]
  · simp [f, Polynomial.aroots_def, hfmonic.leadingCoeff]
  · simp [natDegree_map_eq_of_injective (algebraMap K E).injective g]
  · exact IsAlgClosed.splits _

/-- The discriminant of a power basis is the polynomial discriminant of the
minimal polynomial of its generator. -/
theorem basis_discr_minpoly
    {K L : Type*} [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (pb : PowerBasis K L) :
    Algebra.discr K pb.basis = (minpoly K pb.gen).discr := by
  let f := minpoly K pb.gen
  have hfmonic : f.Monic := minpoly.monic pb.isIntegral_gen
  have hnpos : 0 < f.natDegree := by
    simpa [f] using pb.dim_pos
  have hdegree : 0 < f.degree := natDegree_pos_iff_degree_pos.mp hnpos
  have hderiv : f.derivative.natDegree ≤ f.natDegree - 1 :=
    f.natDegree_derivative_le
  have hpad :
      f.resultant f.derivative f.natDegree (f.natDegree - 1) =
        f.resultant f.derivative := by
    have h := Polynomial.resultant_add_right_deg f f.derivative
      f.natDegree f.derivative.natDegree
      ((f.natDegree - 1) - f.derivative.natDegree) le_rfl
    rw [Nat.add_sub_of_le hderiv, hfmonic.coeff_natDegree, one_pow, one_mul] at h
    exact h
  have hres := Polynomial.resultant_deriv (f := f) hdegree
  rw [hpad, hfmonic.leadingCoeff, mul_one] at hres
  have hfinrank : Module.finrank K L = f.natDegree := by
    calc
      Module.finrank K L = pb.dim := pb.finrank
      _ = f.natDegree := by simp [f]
  change Algebra.discr K pb.basis = f.discr
  rw [Algebra.discr_powerBasis_eq_norm, basis_aeval_resultant,
    hfinrank]
  change (-1) ^ (f.natDegree * (f.natDegree - 1) / 2) *
      f.resultant f.derivative = f.discr
  rw [hres]
  rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

end Submission.NumberTheory.Milne

import Submission.ClassField.FormalGroups.FormalGroupEvaluation

/-!
# Class Field Theory, Chapter I, Section 2: adic evaluation after substitution

Mathlib's general theorem `MvPowerSeries.eval₂_subst` gives the expected
compatibility between substitution and evaluation, but its current interface
puts the discrete topology on the coefficient rings.  That interface cannot
be used when the coefficient ring is also the adically topologized target.

Here we prove the needed same-coefficient version directly.  Substitution is
continuous for the coefficientwise topology because each output coefficient
is a fixed finite sum of input coefficients.  Uniqueness of continuous power
series evaluation then shows that evaluating a substituted series is the
same as evaluating at the values of the substituted coordinates.
-/

namespace Submission.CField.FGroups

open Filter
open scoped MvPowerSeries.WithPiTopology

variable {R : Type*} [CommRing R] [UniformSpace R] [IsTopologicalRing R]

/-- Substitution by an admissible family is continuous for the actual
coefficientwise topology on multivariable power series.  Unlike Mathlib's
`MvPowerSeries.continuous_subst`, this does not require the coefficient ring
to carry the discrete topology. -/
theorem mv_continuous_subst
    {sigma tau : Type*} (a : sigma → MvPowerSeries tau R)
    (ha : MvPowerSeries.HasSubst a) :
    Continuous (MvPowerSeries.subst a :
      MvPowerSeries sigma R → MvPowerSeries tau R) := by
  apply continuous_pi
  intro e
  let c : (sigma →₀ ℕ) → R := fun d ↦
    MvPowerSeries.coeff e (d.prod fun s n ↦ a s ^ n)
  have hc : c.HasFiniteSupport := by
    simpa only [c, MvPowerSeries.coeff_apply, one_smul] using
      MvPowerSeries.coeff_subst_finite ha
        (fun _ : sigma →₀ ℕ ↦ (1 : R)) e
  have heq :
      (fun f : MvPowerSeries sigma R ↦
        MvPowerSeries.subst a f e) =
      fun f ↦ ∑ d ∈ hc.toFinset, MvPowerSeries.coeff d f * c d := by
    funext f
    change MvPowerSeries.coeff e (MvPowerSeries.subst a f) = _
    rw [MvPowerSeries.coeff_subst ha f e]
    apply finsum_eq_sum_of_support_subset
    intro d hd
    rw [Set.Finite.coe_toFinset]
    change c d ≠ 0
    intro hcd
    apply hd
    change MvPowerSeries.coeff d f • c d = 0
    simp only [smul_eq_mul, c] at hcd ⊢
    rw [hcd, mul_zero]
  rw [heq]
  fun_prop

variable [IsUniformAddGroup R] [T2Space R] [CompleteSpace R]
  [IsLinearTopology R R]

/-- Evaluation commutes with an admissible substitution when all rings carry
their actual topology.  The final hypothesis is exactly the convergence
condition for the resulting family of evaluated coordinates. -/
theorem mv_series_eval₂_subst
    {sigma tau : Type*} (a : sigma → MvPowerSeries tau R)
    (ha : MvPowerSeries.HasSubst a) (b : tau → R)
    (hb : MvPowerSeries.HasEval b)
    (hab : MvPowerSeries.HasEval
      (fun s ↦ MvPowerSeries.eval₂ (RingHom.id R) b (a s)))
    (f : MvPowerSeries sigma R) :
    MvPowerSeries.eval₂ (RingHom.id R) b (MvPowerSeries.subst a f) =
      MvPowerSeries.eval₂ (RingHom.id R)
        (fun s ↦ MvPowerSeries.eval₂ (RingHom.id R) b (a s)) f := by
  let epsilon : MvPowerSeries tau R →ₐ[R] R := MvPowerSeries.aeval hb
  have hepsilon : Continuous epsilon := MvPowerSeries.continuous_aeval hb
  have hcontinuous : Continuous
      (fun g : MvPowerSeries sigma R ↦
        MvPowerSeries.eval₂ (RingHom.id R) b (MvPowerSeries.subst a g)) := by
    simpa only [epsilon, MvPowerSeries.coe_aeval, Function.comp_apply] using
      hepsilon.comp (mv_continuous_subst a ha)
  have hunique := MvPowerSeries.eval₂_unique
    (R := R) (S := R) (φ := RingHom.id R)
    (a := fun s ↦ MvPowerSeries.eval₂ (RingHom.id R) b (a s))
    continuous_id hab hcontinuous
    (fun p ↦ by
      rw [MvPowerSeries.subst_coe]
      rw [show RingHom.id R = algebraMap R R by ext; simp]
      rw [← MvPowerSeries.coe_aeval hb]
      rw [MvPolynomial.comp_aeval_apply]
      rfl)
  exact congrFun hunique f

omit [IsLinearTopology R R] in
/-- Finite substitution families whose entries have zero constant
coefficient may be evaluated at an adic point before or after substitution. -/
theorem mv_series_eval₂_subst_of_forall_constantCoeff_zero_adic
    {sigma tau : Type*} [Finite sigma] [Finite tau]
    {I : Ideal R} (hI : IsAdic I)
    (a : sigma → MvPowerSeries tau R)
    (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (b : tau → R) (hb : ∀ i, b i ∈ I)
    (f : MvPowerSeries sigma R) :
    MvPowerSeries.eval₂ (RingHom.id R) b (MvPowerSeries.subst a f) =
      MvPowerSeries.eval₂ (RingHom.id R)
        (fun s ↦ MvPowerSeries.eval₂ (RingHom.id R) b (a s)) f := by
  letI : IsLinearTopology R R :=
    IsLinearTopology.mk_of_hasBasis R hI.hasBasis_nhds_zero
  have ha : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hbEval : MvPowerSeries.HasEval b :=
    mv_forall_adic hI b hb
  have habMem : ∀ s,
      MvPowerSeries.eval₂ (RingHom.id R) b (a s) ∈ I := by
    intro s
    exact mv_constant_adic
      hI (a s) b hb (by rw [ha0 s]; exact I.zero_mem)
  have hab : MvPowerSeries.HasEval
      (fun s ↦ MvPowerSeries.eval₂ (RingHom.id R) b (a s)) :=
    mv_forall_adic hI _ habMem
  exact mv_series_eval₂_subst a ha b hbEval hab f

end Submission.CField.FGroups

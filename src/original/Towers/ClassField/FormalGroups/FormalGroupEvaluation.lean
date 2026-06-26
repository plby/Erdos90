import Towers.ClassField.FormalGroups.Homomorphisms
import Towers.ClassField.FormalGroups.PowerEvalAdic

/-!
# Class Field Theory, Chapter I, after Remark 2.4: evaluating a formal group law

Milne observes that a formal group law over a complete discrete valuation
ring can be evaluated on its maximal ideal and that its value again lies in
the maximal ideal.  We prove the more general ideal-adic statement.  The
multivariable result also supplies the convergence needed for evaluating the
binary law itself.
-/

namespace Towers.CField.FGroups

open Filter

variable {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
  [IsTopologicalRing R] [T2Space R] [CompleteSpace R]

omit [IsUniformAddGroup R] [IsTopologicalRing R] [T2Space R]
  [CompleteSpace R] in
/-- A finite family of elements of an ideal defining the topology is a valid
multivariable power-series evaluation point. -/
theorem mv_forall_adic
    {sigma : Type*} [Finite sigma] {I : Ideal R} (hI : IsAdic I)
    (a : sigma → R) (ha : ∀ i, a i ∈ I) :
    MvPowerSeries.HasEval a where
  hpow i := power_series_adic hI (ha i)
  tendsto_zero := by
    rw [cofinite_eq_bot]
    exact tendsto_bot

/-- Evaluation of a multivariable power series at elements of an adic ideal
lies in that ideal whenever its constant coefficient does. -/
theorem mv_constant_adic
    {sigma : Type*} [Finite sigma] {I : Ideal R} (hI : IsAdic I)
    (f : MvPowerSeries sigma R) (a : sigma → R)
    (ha : ∀ i, a i ∈ I) (hconstant : MvPowerSeries.constantCoeff f ∈ I) :
    MvPowerSeries.eval₂ (RingHom.id R) a f ∈ I := by
  letI : IsLinearTopology R R :=
    IsLinearTopology.mk_of_hasBasis R hI.hasBasis_nhds_zero
  rw [MvPowerSeries.eval₂_eq_tsum continuous_id
    (mv_forall_adic hI a ha)]
  apply tsum_mem
  · have hOpen : IsOpen (I : Set R) := by
      simpa using (isAdic_iff.mp hI).1 1
    exact I.toAddSubgroup.isClosed_of_isOpen hOpen
  · intro d
    by_cases hd : d = 0
    · subst d
      simpa using hconstant
    · obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hd (Finsupp.ext hall)
      have hfactor : a i ^ d i ∈ I := by
        obtain ⟨e, he⟩ := Nat.exists_eq_succ_of_ne_zero hi
        rw [he]
        rw [pow_succ]
        exact I.mul_mem_left _ (ha i)
      have hproduct : d.prod (fun s e => a s ^ e) ∈ I := by
        rw [← d.mul_prod_erase' i (fun s e => a s ^ e) (by simp)]
        exact I.mul_mem_right _ hfactor
      exact I.mul_mem_left _ hproduct

namespace FGLaw

/-- The one-coordinate evaluation point associated to `x`. -/
private def unaryAdicPoint {I : Ideal R} (x : I) : Fin 1 → R :=
  fun _ => x

omit [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [T2Space R] [CompleteSpace R] in
private theorem unary_adic_point {I : Ideal R} (x : I) :
    ∀ i, unaryAdicPoint x i ∈ I :=
  fun _ => x.2

/-- A zero-constant unary series evaluates to an element of an ideal defining
a complete adic topology. -/
noncomputable def adicUnaryValue {I : Ideal R} (hI : IsAdic I)
    (f : UnarySeries R) (hf0 : MvPowerSeries.constantCoeff f = 0)
    (x : I) : I :=
  ⟨MvPowerSeries.eval₂ (RingHom.id R) (unaryAdicPoint x) f,
    mv_constant_adic hI f
      (unaryAdicPoint x) (unary_adic_point x)
      (by rw [hf0]; exact I.zero_mem)⟩

theorem coe_unary_value {I : Ideal R} (hI : IsAdic I)
    (f : UnarySeries R) (hf0 : MvPowerSeries.constantCoeff f = 0)
    (x : I) :
    (adicUnaryValue hI f hf0 x : R) =
      MvPowerSeries.eval₂ (RingHom.id R) (unaryAdicPoint x) f :=
  rfl

/-- The coefficient expansion of a zero-constant unary series converges to
its bundled adic value. -/
theorem adic_unary_value {I : Ideal R} (hI : IsAdic I)
    (f : UnarySeries R) (hf0 : MvPowerSeries.constantCoeff f = 0)
    (x : I) :
    HasSum
      (fun d : Fin 1 →₀ Nat =>
        MvPowerSeries.coeff d f *
          d.prod (fun s e => unaryAdicPoint x s ^ e))
      (adicUnaryValue hI f hf0 x : R) := by
  letI : IsLinearTopology R R :=
    IsLinearTopology.mk_of_hasBasis R hI.hasBasis_nhds_zero
  rw [coe_unary_value]
  exact MvPowerSeries.hasSum_eval₂ continuous_id
    (mv_forall_adic hI
      (unaryAdicPoint x) (unary_adic_point x)) f

/-- The two-coordinate evaluation point associated to `x` and `y`. -/
private def binaryAdicPoint {I : Ideal R} (x y : I) : Fin 2 → R :=
  fun i => if i = 0 then x else y

omit [UniformSpace R] [IsUniformAddGroup R] [IsTopologicalRing R]
  [T2Space R] [CompleteSpace R] in
private theorem binary_adic_point {I : Ideal R} (x y : I) :
    ∀ i, binaryAdicPoint x y i ∈ I := by
  intro i
  simp only [binaryAdicPoint]
  split
  · exact x.2
  · exact y.2

/-- The value `F(x,y)` of a formal group law at two elements of an ideal
defining a complete adic topology, bundled with the proof that it remains in
the ideal. -/
noncomputable def adicValue {I : Ideal R} (hI : IsAdic I)
    (F : FGLaw R) (x y : I) : I :=
  ⟨MvPowerSeries.eval₂ (RingHom.id R)
      (binaryAdicPoint x y) F.law,
    mv_constant_adic hI F.law
      (binaryAdicPoint x y) (binary_adic_point x y)
      (by rw [law_constant_coeff F]; exact I.zero_mem)⟩

theorem coe_adicValue {I : Ideal R} (hI : IsAdic I)
    (F : FGLaw R) (x y : I) :
    (adicValue hI F x y : R) =
      MvPowerSeries.eval₂ (RingHom.id R)
        (binaryAdicPoint x y) F.law :=
  rfl

/-- The multivariable monomial expansion of `F(x,y)` converges to
`adicValue hI F x y`. -/
theorem sum_adic_value {I : Ideal R} (hI : IsAdic I)
    (F : FGLaw R) (x y : I) :
    HasSum
      (fun d : Fin 2 →₀ Nat =>
        MvPowerSeries.coeff d F.law *
          d.prod (fun s e => binaryAdicPoint x y s ^ e))
      (adicValue hI F x y : R) := by
  letI : IsLinearTopology R R :=
    IsLinearTopology.mk_of_hasBasis R hI.hasBasis_nhds_zero
  rw [coe_adicValue]
  exact MvPowerSeries.hasSum_eval₂ continuous_id
    (mv_forall_adic hI
      (binaryAdicPoint x y) (binary_adic_point x y)) F.law

/-- Example 2.5(a) after convergent evaluation: the additive formal law is
ordinary addition. -/
@[simp]
theorem coe_adic_additive {I : Ideal R} (hI : IsAdic I) (x y : I) :
    (adicValue hI (additive (R := R)) x y : R) = (x : R) + y := by
  rw [coe_adicValue]
  change MvPowerSeries.eval₂ (RingHom.id R) (binaryAdicPoint x y)
      (additiveLaw (R := R)) = (x : R) + y
  rw [show additiveLaw (R := R) =
      ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) :
        MvPolynomial (Fin 2) R) : BinarySeries R) from rfl]
  rw [MvPowerSeries.eval₂_coe]
  simp [binaryAdicPoint]

/-- Example 2.5(b) after convergent evaluation: the multiplicative formal law
is `x + y + xy`. -/
@[simp]
theorem coe_value_multiplicative
    {I : Ideal R} (hI : IsAdic I) (x y : I) :
    (adicValue hI (multiplicative (R := R)) x y : R) =
      (x : R) + y + x * y := by
  rw [coe_adicValue]
  change MvPowerSeries.eval₂ (RingHom.id R) (binaryAdicPoint x y)
      (multiplicativeLaw (R := R)) = (x : R) + y + x * y
  rw [show multiplicativeLaw (R := R) =
      ((MvPolynomial.X (0 : Fin 2) + MvPolynomial.X (1 : Fin 2) +
          MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) :
        MvPolynomial (Fin 2) R) : BinarySeries R) from rfl]
  rw [MvPowerSeries.eval₂_coe]
  simp [binaryAdicPoint]

/-- The evaluated form of the isomorphism calculation in Example 2.5(b). -/
theorem coe_adic_multiplicative
    {I : Ideal R} (hI : IsAdic I) (x y : I) :
    1 + (adicValue hI (multiplicative (R := R)) x y : R) =
      (1 + (x : R)) * (1 + (y : R)) := by
  rw [coe_value_multiplicative]
  ring

namespace Hom

/-- Evaluation on an adic ideal of a formal-group homomorphism from
Definition 2.6.  Its zero constant coefficient makes the value land back in
the same ideal. -/
noncomputable def adicValue {I : Ideal R} (hI : IsAdic I)
    {F G : FGLaw R} (f : Hom F G) (x : I) : I :=
  adicUnaryValue hI f.toSeries f.constant_coeff_zero x

theorem coe_adicValue {I : Ideal R} (hI : IsAdic I)
    {F G : FGLaw R} (f : Hom F G) (x : I) :
    (f.adicValue hI x : R) =
      MvPowerSeries.eval₂ (RingHom.id R) (unaryAdicPoint x) f.toSeries :=
  rfl

end Hom

end FGLaw

end Towers.CField.FGroups

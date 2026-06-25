import Submission.Algebra.Magnus.TruncatedMagnusEvaluation


/-!
# Universal unitriangular kernels

This file proves the universal-kernel equality in Efrat--Chapman,
Proposition 5.2.  The key point is that an arbitrary unitriangular
representation evaluates the truncated Magnus expansion: products of `n`
strictly upper-triangular increments vanish in `U_n(R)`.
-/

noncomputable section

namespace EChapma
namespace MSeries

open Finset

variable {R X : Type*} [CommRing R]

/-- An incidence-algebra element has upper degree `k` when it vanishes below
its `k`th superdiagonal. -/
def IncidenceUpperDegree
    {N : ℕ} (k : ℕ) (a : IncidenceAlgebra R (Fin N)) : Prop :=
  ∀ i j, j.1 < i.1 + k → a i j = 0

theorem incidence_upper_mul
    {N a b : ℕ} {u v : IncidenceAlgebra R (Fin N)}
    (hu : IncidenceUpperDegree a u)
    (hv : IncidenceUpperDegree b v) :
    IncidenceUpperDegree (a + b) (u * v) := by
  intro i j hij
  rw [IncidenceAlgebra.mul_apply]
  apply Finset.sum_eq_zero
  intro k _hk
  by_cases hki : k.1 < i.1 + a
  · simp [hu i k hki]
  · simp [hv k j (by omega)]

theorem incidence_upper_neg
    {N k : ℕ} {u : IncidenceAlgebra R (Fin N)}
    (hu : IncidenceUpperDegree k u) :
    IncidenceUpperDegree k (-u) := by
  intro i j hij
  rw [IncidenceAlgebra.neg_apply, hu i j hij, neg_zero]

theorem incidence_upper_degree
    {N : ℕ} :
    IncidenceUpperDegree 0
      (1 : IncidenceAlgebra R (Fin N)) := by
  intro i j hij
  rw [IncidenceAlgebra.one_apply, if_neg (by
    intro h
    subst j
    omega)]

theorem incidence_upper_pow
    {N : ℕ} {u : IncidenceAlgebra R (Fin N)}
    (hu : IncidenceUpperDegree 1 u) :
    ∀ k, IncidenceUpperDegree k (u ^ k)
  | 0 => by
      simpa using
        (incidence_upper_degree
          (R := R) (N := N))
  | k + 1 => by
      rw [pow_succ]
      simpa [Nat.add_comm] using
        incidence_upper_mul
          (incidence_upper_pow hu k) hu

/-- The additive increment of the image of a free generator. -/
def representationIncrement
    {N : ℕ}
    (φ : FreeGroup X →* unitriangularIncidenceSubgroup R N)
    (x : X) :
    IncidenceAlgebra R (Fin N) :=
  ((φ (FreeGroup.of x)).1.1 : IncidenceAlgebra R (Fin N)) - 1

theorem representation_increment_upper
    {N : ℕ}
    (φ : FreeGroup X →* unitriangularIncidenceSubgroup R N)
    (x : X) :
    IncidenceUpperDegree 1 (representationIncrement φ x) := by
  intro i j hij
  by_cases hle : i ≤ j
  · have heq : i = j := by
      apply Fin.ext
      change i.1 = j.1
      omega
    subst j
    simp [representationIncrement, (φ (FreeGroup.of x)).property i]
  · rw [representationIncrement, IncidenceAlgebra.sub_apply,
      IncidenceAlgebra.apply_eq_zero_of_not_le hle,
      IncidenceAlgebra.one_apply, if_neg (by
        intro h
        subst j
        exact hle le_rfl)]
    simp

/-- Evaluate a free word as a product of representation increments. -/
def representationWordEvaluation
    {N : ℕ}
    (φ : FreeGroup X →* unitriangularIncidenceSubgroup R N) :
    FreeMonoid X →* IncidenceAlgebra R (Fin N) :=
  FreeMonoid.lift (representationIncrement φ)

theorem representation_evaluation_upper
    {N : ℕ}
    (φ : FreeGroup X →* unitriangularIncidenceSubgroup R N)
    (w : FreeMonoid X) :
    IncidenceUpperDegree w.length
      (representationWordEvaluation φ w) := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
      intro i j hij
      simp only [FreeMonoid.length_one, Nat.add_zero] at hij
      rw [map_one, IncidenceAlgebra.one_apply, if_neg (by
        intro h
        subst j
        omega)]
  | mul_of x w ih =>
      rw [map_mul, FreeMonoid.length_mul, FreeMonoid.length_of]
      exact incidence_upper_mul
        (representation_increment_upper φ x) ih

theorem representation_evaluation_length
    {N : ℕ}
    (φ : FreeGroup X →* unitriangularIncidenceSubgroup R N)
    (w : FreeMonoid X) (hw : N ≤ w.length) :
    representationWordEvaluation φ w = 0 := by
  apply IncidenceAlgebra.ext
  intro i j _hij
  exact representation_evaluation_upper φ w i j (by
    have hj : j.1 < N := j.isLt
    omega)

theorem incidence_upper_dimension
    {N : ℕ} {u : IncidenceAlgebra R (Fin N)}
    (hu : IncidenceUpperDegree N u) :
    u = 0 := by
  apply IncidenceAlgebra.ext
  intro i j _hij
  exact hu i j (by
    have hj : j.1 < N := j.isLt
    omega)

/-- Evaluation of a noncommutative word polynomial on the increments of an
arbitrary unitriangular representation. -/
def representationPolynomialEvaluation
    {N : ℕ}
    (φ : FreeGroup X →* unitriangularIncidenceSubgroup R N) :
    MonoidAlgebra R (FreeMonoid X) →+*
      IncidenceAlgebra R (Fin N) :=
  MonoidAlgebra.liftNCRingHom
    (algebraMap R (IncidenceAlgebra R (Fin N)))
    (representationWordEvaluation φ)
    (fun r w => Algebra.commutes r
      (representationWordEvaluation φ w))

@[simp]
theorem representation_evaluation_single
    {N : ℕ}
    (φ : FreeGroup X →* unitriangularIncidenceSubgroup R N)
    (w : FreeMonoid X) (r : R) :
    representationPolynomialEvaluation φ
        (MonoidAlgebra.single w r) =
      algebraMap R (IncidenceAlgebra R (Fin N)) r *
        representationWordEvaluation φ w := by
  rw [representationPolynomialEvaluation,
    MonoidAlgebra.liftNCRingHom_single]

theorem representation_evaluation_truncated
    {N : ℕ} [DecidableEq X]
    (φ : FreeGroup X →* unitriangularIncidenceSubgroup R N)
    (p : MonoidAlgebra R (FreeMonoid X))
    (hp :
      magnusRingHom
          (R := R) (X := X) N p = 0) :
    representationPolynomialEvaluation φ p = 0 := by
  have hseries :
      wordPolynomialSeries p ∈
        orderLeastIdeal (R := R) (X := X) N := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa [magnusRingHom,
      series_ring_hom] using hp
  rw [← Finsupp.sum_single p]
  change
    (representationPolynomialEvaluation φ).toAddMonoidHom
        (Finsupp.sum p Finsupp.single) =
      0
  rw [map_finsuppSum]
  rw [Finsupp.sum]
  apply Finset.sum_eq_zero
  intro w _hw
  change
    representationPolynomialEvaluation φ
        (Finsupp.single w (p w)) =
      0
  rw [representation_evaluation_single]
  by_cases hw : w.length < N
  · have hr : p w = 0 := by
      have := hseries w hw
      simpa [word_polynomial_series] using this
    simp [hr]
  · rw [representation_evaluation_length φ w
      (Nat.le_of_not_gt hw)]
    simp

/-- The degree-one polynomial variable corresponding to a free generator. -/
def variablePolynomial
    (x : X) :
    MonoidAlgebra R (FreeMonoid X) :=
  MonoidAlgebra.single (FreeMonoid.of x) 1

@[simp]
theorem series_ring_variable
    [DecidableEq X] (x : X) :
    seriesRingHom
        (R := R) (X := X) (variablePolynomial x) =
      variableSeries (R := R) x := by
  rw [series_ring_hom,
    variablePolynomial, word_series_single,
    GAWt.constantSeries_one, one_mul,
    ← variable_series]

@[simp]
theorem polynomial_evaluation_variable
    {N : ℕ}
    (φ : FreeGroup X →* unitriangularIncidenceSubgroup R N)
    (x : X) :
    representationPolynomialEvaluation φ
        (variablePolynomial x) =
      representationIncrement φ x := by
  rw [variablePolynomial,
    representation_evaluation_single]
  simp [representationWordEvaluation]

theorem magnus_neg_variable
    [DecidableEq X] (N : ℕ) (x : X) :
    magnusRingHom
        (R := R) (X := X) N
        ((-variablePolynomial x) ^ N) =
      0 := by
  rw [magnusRingHom,
    RingHom.comp_apply, map_pow, map_neg,
    series_ring_variable,
    Ideal.Quotient.eq_zero_iff_mem]
  exact pow_vanishesBelow (by simp) N

theorem representation_evaluation_variable
    {N : ℕ}
    (φ : FreeGroup X →* unitriangularIncidenceSubgroup R N)
    (x : X) :
    representationPolynomialEvaluation φ
        ((-variablePolynomial x) ^ N) =
      0 := by
  rw [map_pow, map_neg,
    polynomial_evaluation_variable]
  apply incidence_upper_dimension
  exact incidence_upper_pow
    (incidence_upper_neg
      (representation_increment_upper φ x)) N

/-- The finite geometric polynomial representing the inverse of a Magnus
generator modulo degree `N`. -/
def inverseGeneratorPolynomial
    (N : ℕ) (x : X) :
    MonoidAlgebra R (FreeMonoid X) :=
  ∑ k ∈ Finset.range N, (-variablePolynomial x) ^ k

@[simp]
theorem truncated_magnus_generator
    [DecidableEq X] (N : ℕ) (x : X) :
    magnusRingHom
        (R := R) (X := X) N
        (1 + variablePolynomial x) =
      Ideal.Quotient.mk
        (orderLeastIdeal (R := R) (X := X) N)
        (magnusSeries (R := R) (FreeGroup.of x)) := by
  rw [magnusRingHom,
    RingHom.comp_apply, magnusSeries_of,
    map_add, map_one,
    series_ring_variable]

@[simp]
theorem representation_evaluation_generator
    {N : ℕ}
    (φ : FreeGroup X →* unitriangularIncidenceSubgroup R N)
    (x : X) :
    representationPolynomialEvaluation φ
        (1 + variablePolynomial x) =
      ((φ (FreeGroup.of x)).1.1 :
        IncidenceAlgebra R (Fin N)) := by
  rw [map_add, map_one,
    polynomial_evaluation_variable]
  simp only [representationIncrement]
  noncomm_ring

set_option maxHeartbeats 800000 in
-- Free-group induction expands several nested incidence-algebra coercions.
/-- Every individual Magnus expansion has a finite word-polynomial
representative modulo degree `N`, and every arbitrary unitriangular
representation evaluates that representative to the original group image.
This works for alphabets of arbitrary cardinality. -/
theorem truncated_polynomial_representation
    [DecidableEq X]
    (N : ℕ)
    (φ : FreeGroup X →* unitriangularIncidenceSubgroup R N)
    (g : FreeGroup X) :
    ∃ p : MonoidAlgebra R (FreeMonoid X),
      magnusRingHom
          (R := R) (X := X) N p =
        Ideal.Quotient.mk
          (orderLeastIdeal (R := R) (X := X) N)
          (magnusSeries (R := R) g) ∧
      representationPolynomialEvaluation φ p =
        ((φ g).1.1 : IncidenceAlgebra R (Fin N)) := by
  induction g using FreeGroup.induction_on with
  | C1 =>
      refine ⟨1, ?_, ?_⟩
      · simp
      · simp
  | of x =>
      refine ⟨1 + variablePolynomial x, ?_, ?_⟩
      · exact truncated_magnus_generator N x
      · exact representation_evaluation_generator φ x
  | inv_of x _hx =>
      let p : MonoidAlgebra R (FreeMonoid X) :=
        inverseGeneratorPolynomial N x
      have hgeom :
          p * (1 + variablePolynomial x) =
            1 - (-variablePolynomial x) ^ N := by
        simpa [p, inverseGeneratorPolynomial, sub_neg_eq_add] using
          (geom_sum_mul_neg (-variablePolynomial x) N)
      have hquotientMul :
          magnusRingHom
                (R := R) (X := X) N p *
              magnusRingHom
                (R := R) (X := X) N
                (1 + variablePolynomial x) =
            1 := by
        rw [← map_mul, hgeom, map_sub, map_one,
          magnus_neg_variable,
          sub_zero]
      have hquotientInverse :
          Ideal.Quotient.mk
                (orderLeastIdeal (R := R) (X := X) N)
                (magnusSeries (R := R) (FreeGroup.of x)) *
              Ideal.Quotient.mk
                (orderLeastIdeal (R := R) (X := X) N)
                (magnusSeries (R := R) (FreeGroup.of x)⁻¹) =
            1 := by
        rw [← map_mul, ← magnusSeries_mul]
        simp
      have hpQuotient :
          magnusRingHom
              (R := R) (X := X) N p =
            Ideal.Quotient.mk
              (orderLeastIdeal (R := R) (X := X) N)
              (magnusSeries (R := R) (FreeGroup.of x)⁻¹) := by
        rw [truncated_magnus_generator] at hquotientMul
        calc
          magnusRingHom
                (R := R) (X := X) N p =
              magnusRingHom
                  (R := R) (X := X) N p * 1 := by
                    noncomm_ring
          _ =
              magnusRingHom
                  (R := R) (X := X) N p *
                (Ideal.Quotient.mk
                    (orderLeastIdeal
                      (R := R) (X := X) N)
                    (magnusSeries
                      (R := R) (FreeGroup.of x)) *
                  Ideal.Quotient.mk
                    (orderLeastIdeal
                      (R := R) (X := X) N)
                    (magnusSeries
                      (R := R) (FreeGroup.of x)⁻¹)) := by
                        rw [hquotientInverse]
          _ =
              (magnusRingHom
                    (R := R) (X := X) N p *
                  Ideal.Quotient.mk
                    (orderLeastIdeal
                      (R := R) (X := X) N)
                    (magnusSeries
                      (R := R) (FreeGroup.of x))) *
                Ideal.Quotient.mk
                  (orderLeastIdeal
                    (R := R) (X := X) N)
                  (magnusSeries
                    (R := R) (FreeGroup.of x)⁻¹) := by
                      noncomm_ring
          _ =
              Ideal.Quotient.mk
                (orderLeastIdeal (R := R) (X := X) N)
                (magnusSeries
                  (R := R) (FreeGroup.of x)⁻¹) := by
                    rw [hquotientMul]
                    noncomm_ring
      have hevaluationMul :
          representationPolynomialEvaluation φ p *
              representationPolynomialEvaluation φ
                (1 + variablePolynomial x) =
            1 := by
        rw [← map_mul, hgeom, map_sub, map_one,
          representation_evaluation_variable,
          sub_zero]
      have hrepresentationInverse :
          (((φ (FreeGroup.of x)).1.1 :
                IncidenceAlgebra R (Fin N)) *
              ((φ (FreeGroup.of x)⁻¹).1.1 :
                IncidenceAlgebra R (Fin N))) =
            1 := by
        simp
      have hpEvaluation :
          representationPolynomialEvaluation φ p =
            ((φ (FreeGroup.of x)⁻¹).1.1 :
              IncidenceAlgebra R (Fin N)) := by
        rw [representation_evaluation_generator] at hevaluationMul
        calc
          representationPolynomialEvaluation φ p =
              representationPolynomialEvaluation φ p * 1 := by
                noncomm_ring
          _ =
              representationPolynomialEvaluation φ p *
                (((φ (FreeGroup.of x)).1.1 :
                    IncidenceAlgebra R (Fin N)) *
                  ((φ (FreeGroup.of x)⁻¹).1.1 :
                    IncidenceAlgebra R (Fin N))) := by
                      rw [hrepresentationInverse]
          _ =
              (representationPolynomialEvaluation φ p *
                  ((φ (FreeGroup.of x)).1.1 :
                    IncidenceAlgebra R (Fin N))) *
                ((φ (FreeGroup.of x)⁻¹).1.1 :
                  IncidenceAlgebra R (Fin N)) := by
                    noncomm_ring
          _ =
              ((φ (FreeGroup.of x)⁻¹).1.1 :
                IncidenceAlgebra R (Fin N)) := by
                  rw [hevaluationMul]
                  noncomm_ring
      exact ⟨p, hpQuotient, hpEvaluation⟩
  | mul g h ihg ihh =>
      obtain ⟨p, hpQ, hpE⟩ := ihg
      obtain ⟨q, hqQ, hqE⟩ := ihh
      refine ⟨p * q, ?_, ?_⟩
      · rw [map_mul, hpQ, hqQ, ← map_mul,
          ← magnusSeries_mul]
      · rw [map_mul, hpE, hqE]
        change
          (((φ g * φ h).1.1 :
              IncidenceAlgebra R (Fin N))) =
            ((φ (g * h)).1.1 :
              IncidenceAlgebra R (Fin N))
        have hsub :
            (φ g * φ h).1 = (φ (g * h)).1 :=
          congrArg Subtype.val (φ.map_mul g h).symm
        exact congrArg Units.val hsub

/-- The intersection of the kernels of all homomorphisms from the free group
to `U_N(R)`. -/
def unitriangularKernelIntersection
    (N : ℕ) :
    Subgroup (FreeGroup X) :=
  ⨅ φ : FreeGroup X →*
      unitriangularIncidenceSubgroup R N,
    MonoidHom.ker φ

theorem subgroup_unitriangular_intersection
    (N : ℕ) :
    magnusOrderSubgroup (R := R) (X := X) N ≤
      unitriangularKernelIntersection
        (R := R) (X := X) N := by
  intro g hg
  classical
  change
    g ∈ ⨅ φ : FreeGroup X →*
        unitriangularIncidenceSubgroup R N,
      MonoidHom.ker φ
  rw [Subgroup.mem_iInf]
  intro φ
  obtain ⟨p, hpQ, hpE⟩ :=
    truncated_polynomial_representation N φ g
  have hMagnusOne :
      Ideal.Quotient.mk
          (orderLeastIdeal (R := R) (X := X) N)
          (magnusSeries (R := R) g) =
        1 := by
    apply Ideal.Quotient.eq.mpr
    change
      magnusSeries (R := R) g - 1 ∈
        orderLeastIdeal (R := R) (X := X) N
    exact hg
  have hpOne :
      magnusRingHom
          (R := R) (X := X) N p =
        1 := hpQ.trans hMagnusOne
  have hpSubOne :
      magnusRingHom
          (R := R) (X := X) N (p - 1) =
        0 := by
    rw [map_sub, hpOne, map_one, sub_self]
  have hevalSubOne :=
    representation_evaluation_truncated
      φ (p - 1) hpSubOne
  have hpEvalOne :
      representationPolynomialEvaluation φ p = 1 := by
    rw [map_sub, map_one] at hevalSubOne
    exact sub_eq_zero.mp hevalSubOne
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  apply Units.ext
  exact hpE.symm.trans hpEvalOne

/-- Efrat--Chapman, Proposition 5.2: Magnus order `N` is the intersection
of the kernels of all homomorphisms to `U_N(R)`, equivalently the
intersection of the canonical word-representation kernels. -/
theorem order_unitriangular_intersection
    (N : ℕ) (hN : 1 ≤ N) :
    magnusOrderSubgroup (R := R) (X := X) N =
      unitriangularKernelIntersection
        (R := R) (X := X) N := by
  apply le_antisymm
  · exact
      subgroup_unitriangular_intersection N
  · intro g hg
    rw [magnus_coefficient_intersection
      (R := R) (X := X) N hN]
    change
      g ∈ ⨅ xs : {xs : List X // xs.length = N - 1},
        MonoidHom.ker
          (wordCoefficientRepresentation (R := R) xs.1)
    rw [Subgroup.mem_iInf]
    intro xs
    have hdim : xs.1.length + 1 = N := by
      omega
    have hg' :
        g ∈ unitriangularKernelIntersection
          (R := R) (X := X) (xs.1.length + 1) := by
      rw [hdim]
      exact hg
    exact
      (Subgroup.mem_iInf.mp hg')
        (wordCoefficientRepresentation (R := R) xs.1)

end MSeries
end EChapma

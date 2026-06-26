import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Milne, Chapter 3, Exercise 4

For a field `k`, let `A = k[X², X³]` inside `k[X]`.  This ring is Noetherian and every
nonzero prime ideal is maximal, but it is not integrally closed and hence is not a Dedekind
domain.

For the dimension argument, we regard `A` as an algebra over another polynomial ring by sending
its variable to `X²`.  The extension is integral because the other generator `X³` has square in
the image.  For non-normality, every element of `A` has zero linear coefficient; consequently
`X² ∤ X³` in `A`, although `(X²)² ∣ (X³)²`.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

noncomputable section

variable (k : Type*) [Field k]

/-- The endomorphism of `k[X]` sending the variable to its square. -/
def SquareEndomorphism : k[X] →ₐ[k] k[X] :=
  Polynomial.aeval (X ^ 2)

/-- Milne's first observation in part (a): with scalars acting by `T ↦ X²`, the polynomial
ring `k[X]` is a finite module over `k[T]`. -/
theorem polynomial_finite_squares :
    @Module.Finite k[X] k[X] _ _
      (SquareEndomorphism k).toRingHom.toAlgebra.toModule := by
  letI : Algebra k[X] k[X] := (SquareEndomorphism k).toRingHom.toAlgebra
  have hX : IsIntegral k[X] (X : k[X]) := by
    refine ⟨X ^ 2 - C X, monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
    change X ^ 2 - SquareEndomorphism k X = 0
    simp [SquareEndomorphism]
  have hIntegral : Algebra.IsIntegral k[X] k[X] := by
    refine ⟨fun p => ?_⟩
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact hp.add hq
    | monomial n a =>
        rw [← C_mul_X_pow_eq_monomial]
        have hC : IsIntegral k[X] (C a : k[X]) := by
          rw [show (C a : k[X]) = algebraMap k[X] k[X] (C a) by
            change C a = SquareEndomorphism k (C a)
            simp [SquareEndomorphism]]
          exact isIntegral_algebraMap
        have hpow : IsIntegral k[X] ((X : k[X]) ^ n) := by
          induction n with
          | zero => simpa using (isIntegral_one : IsIntegral k[X] (1 : k[X]))
          | succ n hn => simpa [pow_succ] using hn.mul hX
        exact hC.mul hpow
  have htop : Algebra.adjoin k[X] ({(X : k[X])} : Set k[X]) = ⊤ := by
    refine top_unique ?_
    intro p hp
    clear hp
    induction p using Polynomial.induction_on' with
    | add p q hp hq => exact (Algebra.adjoin k[X] ({X} : Set k[X])).add_mem hp hq
    | monomial n a =>
        rw [← C_mul_X_pow_eq_monomial]
        apply (Algebra.adjoin k[X] ({X} : Set k[X])).mul_mem
        · rw [show (C a : k[X]) = algebraMap k[X] k[X] (C a) by
            change C a = SquareEndomorphism k (C a)
            simp [SquareEndomorphism]]
          exact (Algebra.adjoin k[X] ({X} : Set k[X])).algebraMap_mem (C a)
        · exact (Algebra.adjoin k[X] ({X} : Set k[X])).pow_mem
            (Algebra.subset_adjoin rfl) n
  letI : Algebra.FiniteType k[X] k[X] :=
    ⟨⟨{X}, by simpa using htop⟩⟩
  letI : Algebra.IsIntegral k[X] k[X] := hIntegral
  exact Algebra.IsIntegral.finite

/-- The cusp ring `k[X², X³]`, as a subalgebra of `k[X]`. -/
abbrev CuspRing :=
  Algebra.adjoin k ({(X : k[X]) ^ 2, X ^ 3} : Set k[X])

/-- The element `X²` of the cusp ring. -/
def cuspidalDedekind4 : CuspRing k :=
  ⟨X ^ 2, Algebra.subset_adjoin (Set.mem_insert _ _)⟩

/-- The element `X³` of the cusp ring. -/
def cuspidal43 : CuspRing k :=
  ⟨X ^ 3, Algebra.subset_adjoin (Set.mem_insert_iff.mpr (Or.inr rfl))⟩

/-- The map `k[T] → k[X², X³]` taking `T` to `X²`. -/
def SquareAlgHom : k[X] →ₐ[k] CuspRing k :=
  Polynomial.aeval (cuspidalDedekind4 k)

theorem square_hom_x :
    SquareAlgHom k X = cuspidalDedekind4 k := by
  simp [SquareAlgHom]

theorem square_alg_x (n : ℕ) :
    SquareAlgHom k (X ^ n) = (cuspidalDedekind4 k) ^ n := by
  simp [SquareAlgHom]

/-- Part (a): the cusp ring is Noetherian. -/
theorem cuspidalDedekindisNoetherian : IsNoetherianRing (CuspRing k) := by
  letI : Algebra.FiniteType k (CuspRing k) :=
    Algebra.FiniteType.adjoin_of_finite
      ((Set.finite_singleton ((X : k[X]) ^ 3)).insert (X ^ 2))
  exact Algebra.FiniteType.isNoetherianRing k (CuspRing k)

private theorem x_3_cube :
    (cuspidal43 k) ^ 2 = SquareAlgHom k (X ^ 3) := by
  apply Subtype.ext
  simp [cuspidalDedekind4, cuspidal43, SquareAlgHom]
  ring

/-- The extension `k[T] → k[X², X³]`, `T ↦ X²`, is integral. -/
theorem integral_square_alg :
    letI : Algebra k[X] (CuspRing k) :=
      (SquareAlgHom k).toRingHom.toAlgebra
    Algebra.IsIntegral k[X] (CuspRing k) := by
  letI : Algebra k[X] (CuspRing k) :=
    (SquareAlgHom k).toRingHom.toAlgebra
  refine ⟨fun z => ?_⟩
  refine Algebra.adjoin_induction
    (p := fun q hq => IsIntegral k[X] (⟨q, hq⟩ : CuspRing k)) ?_ ?_ ?_ ?_
    z.property
  · intro p hp
    rcases hp with (rfl | hp)
    · change IsIntegral k[X] (cuspidalDedekind4 k)
      rw [show cuspidalDedekind4 k = algebraMap k[X] (CuspRing k) X by
        exact (square_hom_x k).symm]
      exact isIntegral_algebraMap
    · have hp : p = (X : k[X]) ^ 3 := by simpa using hp
      subst p
      change IsIntegral k[X] (cuspidal43 k)
      apply IsIntegral.of_pow (n := 2) (by norm_num)
      rw [x_3_cube]
      exact isIntegral_algebraMap
  · intro r
    convert (isIntegral_algebraMap : IsIntegral k[X]
      (algebraMap k[X] (CuspRing k) (C r))) using 1
    apply Subtype.ext
    change C r = SquareAlgHom k (C r)
    simp [SquareAlgHom]
  · intro x y hx hy hxi hyi
    exact hxi.add hyi
  · intro x y hx hy hxi hyi
    exact hxi.mul hyi

/-- Part (b): every nonzero prime ideal of the cusp ring is maximal. -/
theorem prime_isMaximal
    (P : Ideal (CuspRing k)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    P.IsMaximal := by
  letI : Algebra k[X] (CuspRing k) :=
    (SquareAlgHom k).toRingHom.toAlgebra
  letI : Algebra.IsIntegral k[X] (CuspRing k) :=
    integral_square_alg k
  letI : P.IsPrime := hP
  have hcomap0 : P.comap (algebraMap k[X] (CuspRing k)) ≠ ⊥ := by
    intro h
    exact hP0 (Ideal.eq_bot_of_comap_eq_bot h)
  have hcomapMax :
      (P.comap (algebraMap k[X] (CuspRing k))).IsMaximal :=
    (P.comap_isPrime (algebraMap k[X] (CuspRing k))).isMaximal hcomap0
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P hcomapMax

/-- Equivalently, the cusp ring has Krull dimension at most one. -/
theorem dimensionLEOne : Ring.DimensionLEOne (CuspRing k) where
  maximalOfPrime := fun hP0 hP => prime_isMaximal k _ hP hP0

/-- Every polynomial in `k[X², X³]` has zero coefficient of `X`. -/
theorem one_zero (p : CuspRing k) :
    (p : k[X]).coeff 1 = 0 := by
  refine Algebra.adjoin_induction (p := fun q _ => q.coeff 1 = 0) ?_ ?_ ?_ ?_ p.property
  · intro q hq
    rcases hq with (rfl | hq)
    · simp
    · have hq : q = (X : k[X]) ^ 3 := by simpa using hq
      subst q
      simp
  · intro r
    simp
  · intro x y hx hy hxi hyi
    simp [hxi, hyi]
  · intro x y hx hy hxi hyi
    simp [Polynomial.mul_coeff_one, hxi, hyi]

/-- The element `X²` does not divide `X³` inside the cusp ring. -/
theorem x_dvd_3 :
    ¬cuspidalDedekind4 k ∣ cuspidal43 k := by
  rintro ⟨c, hc⟩
  have hcoeff := congrArg (fun p : k[X] => p.coeff 3) (congrArg Subtype.val hc)
  have hc1 := one_zero k c
  have hshift : ((X : k[X]) ^ 2 * (c : k[X])).coeff 3 = (c : k[X]).coeff 1 := by
    simpa using Polynomial.coeff_X_pow_mul (c : k[X]) 2 1
  simp only [cuspidalDedekind4, cuspidal43, Subtype.coe_mk, coeff_X_pow,
    if_true] at hcoeff
  change 1 = ((X : k[X]) ^ 2 * (c : k[X])).coeff 3 at hcoeff
  rw [hshift, hc1] at hcoeff
  exact one_ne_zero hcoeff

/-- Nevertheless, the square of `X²` divides the square of `X³`. -/
theorem x_sq_3 :
    (cuspidalDedekind4 k) ^ 2 ∣ (cuspidal43 k) ^ 2 := by
  refine ⟨cuspidalDedekind4 k, ?_⟩
  apply Subtype.ext
  simp [cuspidalDedekind4, cuspidal43]
  ring

/-- The cusp ring is not integrally closed. -/
theorem not_integrally_closed :
    ¬IsIntegrallyClosed (CuspRing k) := by
  intro h
  letI : IsIntegrallyClosed (CuspRing k) := h
  exact x_dvd_3 k
    ((IsIntegrallyClosed.pow_dvd_pow_iff (R := CuspRing k)
      (n := 2) (by norm_num)).mp (x_sq_3 k))

/-- Thus `k[X², X³]` is not a Dedekind domain. -/
theorem cuspidal_dedekindnot_domain :
    ¬IsDedekindDomain (CuspRing k) := by
  intro h
  letI : IsDedekindDomain (CuspRing k) := h
  exact not_integrally_closed k inferInstance

end

end Towers.NumberTheory.Milne

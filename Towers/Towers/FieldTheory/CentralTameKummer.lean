import Towers.FieldTheory.CentralEmbeddingLocal
import Mathlib.FieldTheory.KummerExtension


/-!
# Semilinear lifts on tame Kummer radicals

This file supplies the arbitrary-degree version of the cubic semilinear
construction used for central embedding problems.  It is the algebraic core
of the standard realization of a finite tame metacyclic group.
-/

noncomputable section

namespace Towers
namespace TBluepr

open Polynomial AdjoinRoot

universe u

/-- The Kummer polynomial `X^e - a`. -/
def tameKummerPolynomial {L : Type u} [Field L]
    (e : ℕ) (a : Lˣ) : L[X] :=
  X ^ e - C (a : L)

/-- The radical algebra obtained by adjoining an `e`th root of `a`. -/
abbrev TameKummerAdjoin {L : Type u} [Field L]
    (e : ℕ) (a : Lˣ) :=
  AdjoinRoot (tameKummerPolynomial e a)

section

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

instance tameKummerDimensional
    (e : ℕ) [NeZero e] (a : Lˣ) :
    FiniteDimensional K (TameKummerAdjoin e a) := by
  let hmonic : (tameKummerPolynomial e a).Monic := by
    simpa [tameKummerPolynomial] using
      (monic_X_pow_sub_C (a : L) (NeZero.ne e))
  letI : Module.Finite L (TameKummerAdjoin e a) :=
    hmonic.finite_adjoinRoot
  exact Module.Finite.trans L (TameKummerAdjoin e a)

/-- A Galois automorphism of `L/K` extends across an `e`th radical whenever
the multiplier has the required `e`th power. -/
noncomputable def tameKummerSemilinear
    (e : ℕ) [NeZero e] (a : Lˣ)
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ e) :
    TameKummerAdjoin e a →ₐ[K] TameKummerAdjoin e a := by
  let N := TameKummerAdjoin e a
  let i : L →ₐ[K] N :=
    (IsScalarTower.toAlgHom K L N).comp sigma.toAlgHom
  let x : N := algebraMap L N (b : L) * root (tameKummerPolynomial e a)
  refine AdjoinRoot.liftAlgHom (S := K) (R := L) (T := N)
    (tameKummerPolynomial e a) i x ?_
  simp only [tameKummerPolynomial, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_C]
  dsimp [x, i]
  rw [mul_pow, ← map_pow]
  rw [show root (tameKummerPolynomial e a) ^ e =
      algebraMap L N (a : L) by
    simpa [tameKummerPolynomial] using
      root_X_pow_sub_C_pow e (a : L)]
  rw [← map_mul, ← map_sub]
  have hb' := hb
  change Units.map sigma.toRingEquiv.toMonoidHom a / a = b ^ e at hb'
  have hu : b ^ e * a = Units.map sigma.toRingEquiv.toMonoidHom a := by
    calc
      b ^ e * a =
          (Units.map sigma.toRingEquiv.toMonoidHom a / a) * a := by rw [hb']
      _ = Units.map sigma.toRingEquiv.toMonoidHom a := div_mul_cancel _ _
  rw [show (b : L) ^ e * (a : L) - sigma (a : L) = 0 by
    apply sub_eq_zero.mpr
    exact congrArg Units.val hu, map_zero]

omit [FiniteDimensional K L] in
@[simp]
theorem tame_semilinear_lift
    (e : ℕ) [NeZero e] (a : Lˣ)
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ e) (y : L) :
    tameKummerSemilinear e a sigma b hb
        (AdjoinRoot.of (tameKummerPolynomial e a) y) =
      AdjoinRoot.of (tameKummerPolynomial e a) (sigma y) := by
  simp [tameKummerSemilinear]

omit [FiniteDimensional K L] in
@[simp]
theorem tame_semilinear_root
    (e : ℕ) [NeZero e] (a : Lˣ)
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ e) :
    tameKummerSemilinear e a sigma b hb
        (root (tameKummerPolynomial e a)) =
      algebraMap L (TameKummerAdjoin e a) (b : L) *
        root (tameKummerPolynomial e a) := by
  simp [tameKummerSemilinear]

/-- Under irreducibility, the semilinear endomorphism is an automorphism. -/
noncomputable def tameSemilinearLift
    (e : ℕ) [NeZero e] (a : Lˣ)
    (hirr : Irreducible (tameKummerPolynomial e a))
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ e) :
    TameKummerAdjoin e a ≃ₐ[K] TameKummerAdjoin e a := by
  letI : Fact (Irreducible (tameKummerPolynomial e a)) := ⟨hirr⟩
  let hom := tameKummerSemilinear e a sigma b hb
  apply AlgEquiv.ofBijective hom
  have hinjective : Function.Injective hom := RingHom.injective hom.toRingHom
  refine ⟨hinjective, ?_⟩
  have hlinearInjective : Function.Injective hom.toLinearMap := hinjective
  exact LinearMap.injective_iff_surjective.mp hlinearInjective

@[simp]
theorem tame_kummer_lift
    (e : ℕ) [NeZero e] (a : Lˣ)
    (hirr : Irreducible (tameKummerPolynomial e a))
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ e) (y : L) :
    tameSemilinearLift e a hirr sigma b hb
        (AdjoinRoot.of (tameKummerPolynomial e a) y) =
      AdjoinRoot.of (tameKummerPolynomial e a) (sigma y) :=
  by
    change tameKummerSemilinear e a sigma b hb
        (AdjoinRoot.of (tameKummerPolynomial e a) y) = _
    exact tame_semilinear_lift e a sigma b hb y

@[simp]
theorem semilinear_lift_root
    (e : ℕ) [NeZero e] (a : Lˣ)
    (hirr : Irreducible (tameKummerPolynomial e a))
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ e) :
    tameSemilinearLift e a hirr sigma b hb
        (root (tameKummerPolynomial e a)) =
      algebraMap L (TameKummerAdjoin e a) (b : L) *
        root (tameKummerPolynomial e a) :=
  by
    change tameKummerSemilinear e a sigma b hb
        (root (tameKummerPolynomial e a)) = _
    exact tame_semilinear_root e a sigma b hb

@[simp]
theorem tame_kummer_semilinear
    (e : ℕ) [NeZero e] (a : Lˣ)
    (hirr : Irreducible (tameKummerPolynomial e a))
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ e) (y : L) :
    tameSemilinearLift e a hirr sigma b hb
        (algebraMap L (TameKummerAdjoin e a) y) =
      algebraMap L (TameKummerAdjoin e a) (sigma y) := by
  simpa only [AdjoinRoot.algebraMap_eq] using
    tame_kummer_lift e a hirr sigma b hb y

/-- Transporting the coefficient automorphism does not change a semilinear
lift; the radical identity is proposition-valued. -/
theorem tame_semilinear_congr
    (e : ℕ) [NeZero e] (a : Lˣ)
    (hirr : Irreducible (tameKummerPolynomial e a))
    {sigma tau : Gal(L/K)} (h : sigma = tau) (b : Lˣ)
    (hSigma : sigma • a / a = b ^ e)
    (hTau : tau • a / a = b ^ e) :
    tameSemilinearLift e a hirr sigma b hSigma =
      tameSemilinearLift e a hirr tau b hTau := by
  subst tau
  rfl

/-- An `e`th root of unity scales the chosen radical and fixes `L`. -/
noncomputable def tameScalarAut
    (e : ℕ) [NeZero e] (a : Lˣ)
    (hirr : Irreducible (tameKummerPolynomial e a))
    (z : Lˣ) (hz : z ^ e = 1) :
    TameKummerAdjoin e a ≃ₐ[K] TameKummerAdjoin e a :=
  tameSemilinearLift e a hirr (1 : Gal(L/K)) z (by simp [hz])

@[simp]
theorem tame_aut
    (e : ℕ) [NeZero e] (a : Lˣ)
    (hirr : Irreducible (tameKummerPolynomial e a))
    (z : Lˣ) (hz : z ^ e = 1) (y : L) :
    tameScalarAut (K := K) (L := L) e a hirr z hz
        (AdjoinRoot.of (tameKummerPolynomial e a) y) =
      AdjoinRoot.of (tameKummerPolynomial e a) y := by
  simp [tameScalarAut]

@[simp]
theorem tame_scalar_aut
    (e : ℕ) [NeZero e] (a : Lˣ)
    (hirr : Irreducible (tameKummerPolynomial e a))
    (z : Lˣ) (hz : z ^ e = 1) (y : L) :
    tameScalarAut (K := K) (L := L) e a hirr z hz
        (algebraMap L (TameKummerAdjoin e a) y) =
      algebraMap L (TameKummerAdjoin e a) y := by
  simp [tameScalarAut]

@[simp]
theorem tame_kummer_aut
    (e : ℕ) [NeZero e] (a : Lˣ)
    (hirr : Irreducible (tameKummerPolynomial e a))
    (z : Lˣ) (hz : z ^ e = 1) :
    tameScalarAut (K := K) (L := L) e a hirr z hz
        (root (tameKummerPolynomial e a)) =
      algebraMap L (TameKummerAdjoin e a) (z : L) *
        root (tameKummerPolynomial e a) := by
  simp [tameScalarAut]

theorem tame_kummer_scalar
    (e : ℕ) [NeZero e] (a : Lˣ)
    (hirr : Irreducible (tameKummerPolynomial e a))
    (h1 : (1 : Lˣ) ^ e = 1) :
    tameScalarAut (K := K) (L := L) e a hirr 1 h1 = 1 := by
  apply AlgEquiv.coe_algHom_injective
  apply AdjoinRoot.algHom_ext'
  · ext y
    simp
  · simp [tame_kummer_aut]

/-- Semilinear radical lifts multiply with the expected root-of-unity
factor. -/
theorem tame_semilinear_mul
    (e : ℕ) [NeZero e] (a : Lˣ)
    (hirr : Irreducible (tameKummerPolynomial e a))
    (sigma tau : Gal(L/K)) (bSigma bTau bMul z : Lˣ)
    (hSigma : sigma • a / a = bSigma ^ e)
    (hTau : tau • a / a = bTau ^ e)
    (hMul : (sigma * tau) • a / a = bMul ^ e)
    (hz : z ^ e = 1)
    (hc : sigma • bTau / bMul * bSigma = z) :
    tameSemilinearLift e a hirr sigma bSigma hSigma *
        tameSemilinearLift e a hirr tau bTau hTau =
      tameScalarAut (K := K) (L := L) e a hirr z hz *
        tameSemilinearLift e a hirr (sigma * tau) bMul hMul := by
  apply AlgEquiv.coe_algHom_injective
  apply AdjoinRoot.algHom_ext'
  · ext y
    simp
  · have hc' := hc
    change Units.map sigma.toRingEquiv.toMonoidHom bTau /
      bMul * bSigma = z at hc'
    simp only [div_eq_mul_inv] at hc'
    have hcoeff :
        Units.map sigma.toRingEquiv.toMonoidHom bTau * bSigma =
          z * bMul := by
      have hmul := congrArg (fun w : Lˣ ↦ w * bMul) hc'
      calc
        Units.map sigma.toRingEquiv.toMonoidHom bTau * bSigma =
            (Units.map sigma.toRingEquiv.toMonoidHom bTau * bMul⁻¹ *
              bSigma) * bMul := by
                calc
                  Units.map sigma.toRingEquiv.toMonoidHom bTau * bSigma =
                      (bMul⁻¹ * bMul) *
                        (Units.map sigma.toRingEquiv.toMonoidHom bTau *
                          bSigma) := by simp
                  _ = (Units.map sigma.toRingEquiv.toMonoidHom bTau *
                        bMul⁻¹ * bSigma) * bMul := by ac_rfl
        _ = z * bMul := hmul
    change
      tameSemilinearLift e a hirr sigma bSigma hSigma
          (tameSemilinearLift e a hirr tau bTau hTau
            (root (tameKummerPolynomial e a))) =
        tameScalarAut (K := K) (L := L) e a hirr z hz
          (tameSemilinearLift e a hirr (sigma * tau) bMul hMul
            (root (tameKummerPolynomial e a)))
    rw [semilinear_lift_root, map_mul,
      tame_kummer_semilinear,
      semilinear_lift_root, semilinear_lift_root,
      map_mul, tame_scalar_aut, tame_kummer_aut]
    have hcoeffVal :
        sigma (bTau : L) * (bSigma : L) = (z : L) * (bMul : L) :=
      congrArg Units.val hcoeff
    calc
      algebraMap L (TameKummerAdjoin e a) (sigma (bTau : L)) *
            (algebraMap L (TameKummerAdjoin e a) (bSigma : L) *
              root (tameKummerPolynomial e a)) =
          algebraMap L (TameKummerAdjoin e a)
              (sigma (bTau : L) * (bSigma : L)) *
            root (tameKummerPolynomial e a) := by rw [map_mul, mul_assoc]
      _ = algebraMap L (TameKummerAdjoin e a)
              ((z : L) * (bMul : L)) *
            root (tameKummerPolynomial e a) := by rw [hcoeffVal]
      _ = algebraMap L (TameKummerAdjoin e a) (bMul : L) *
            (algebraMap L (TameKummerAdjoin e a) (z : L) *
              root (tameKummerPolynomial e a)) := by
            rw [map_mul]
            ac_rfl

/-- If the root scalars satisfy the semilinear cocycle equation, the lifts
multiply strictly. -/
theorem tame_semilinear_cocycle
    (e : ℕ) [NeZero e] (a : Lˣ)
    (hirr : Irreducible (tameKummerPolynomial e a))
    (sigma tau : Gal(L/K)) (bSigma bTau bMul : Lˣ)
    (hSigma : sigma • a / a = bSigma ^ e)
    (hTau : tau • a / a = bTau ^ e)
    (hMul : (sigma * tau) • a / a = bMul ^ e)
    (hc : bMul = sigma • bTau * bSigma) :
    tameSemilinearLift e a hirr sigma bSigma hSigma *
        tameSemilinearLift e a hirr tau bTau hTau =
      tameSemilinearLift e a hirr (sigma * tau) bMul hMul := by
  have hc' : sigma • bTau / bMul * bSigma = (1 : Lˣ) := by
    rw [hc, div_mul_cancel_left, inv_mul_cancel]
  have h := tame_semilinear_mul e a hirr sigma tau
    bSigma bTau bMul 1 hSigma hTau hMul (by simp) hc'
  rw [tame_kummer_scalar (K := K) (L := L), one_mul] at h
  exact h

end

end TBluepr
end Towers

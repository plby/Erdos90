import Towers.FieldTheory.CentralEmbeddingBrauer


/-!
# Kummer realization of a central cubic embedding obstruction

This file constructs the semilinear automorphisms used to turn a trivial
cube-root-valued factor set into a weak solution of a central embedding
problem.
-/

noncomputable section

namespace Towers
namespace TBluepr

open Polynomial AdjoinRoot
open Towers.CField.CProduca

universe u v w

/-- The cubic Kummer polynomial attached to a unit. -/
def cubicKummerPolynomial {L : Type u} [Field L] (a : Lˣ) : L[X] :=
  X ^ 3 - C (a : L)

/-- The simple cubic radical algebra attached to a unit. -/
abbrev CubicKummerAdjoin {L : Type u} [Field L] (a : Lˣ) :=
  AdjoinRoot (cubicKummerPolynomial a)

section

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L]

instance cubicKummerDimensional (a : Lˣ) :
    FiniteDimensional K (CubicKummerAdjoin a) := by
  let hmonic : (cubicKummerPolynomial a).Monic := by
    simpa [cubicKummerPolynomial] using
      (monic_X_pow_sub_C (a : L) (by norm_num : (3 : ℕ) ≠ 0))
  letI : Module.Finite L (CubicKummerAdjoin a) :=
    hmonic.finite_adjoinRoot
  exact Module.Finite.trans L (CubicKummerAdjoin a)

variable (a : Lˣ)

/-- A Galois automorphism of the coefficient field, together with a scalar
whose cube is `sigma(a) / a`, extends over the cubic radical by sending the
chosen root to that scalar times the root. -/
noncomputable def cubicKummerSemilinear
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ 3) :
    CubicKummerAdjoin a →ₐ[K] CubicKummerAdjoin a := by
  let N := CubicKummerAdjoin a
  let i : L →ₐ[K] N :=
    (IsScalarTower.toAlgHom K L N).comp sigma.toAlgHom
  let x : N := algebraMap L N (b : L) * root (cubicKummerPolynomial a)
  refine AdjoinRoot.liftAlgHom (S := K) (R := L) (T := N)
    (cubicKummerPolynomial a) i x ?_
  simp only [cubicKummerPolynomial, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  dsimp [x, i]
  rw [mul_pow]
  rw [← map_pow]
  rw [show root (cubicKummerPolynomial a) ^ 3 =
      algebraMap L N (a : L) by
    simpa [cubicKummerPolynomial] using
      root_X_pow_sub_C_pow 3 (a : L)]
  rw [← map_mul, ← map_sub]
  have hb' := hb
  change Units.map sigma.toRingEquiv.toMonoidHom a / a = b ^ 3 at hb'
  have hu : b ^ 3 * a = Units.map sigma.toRingEquiv.toMonoidHom a := by
    calc
      b ^ 3 * a =
          (Units.map sigma.toRingEquiv.toMonoidHom a / a) * a := by rw [hb']
      _ = Units.map sigma.toRingEquiv.toMonoidHom a := div_mul_cancel _ _
  rw [show (b : L) ^ 3 * (a : L) - sigma (a : L) = 0 by
    apply sub_eq_zero.mpr
    exact congrArg Units.val hu, map_zero]

omit [FiniteDimensional K L] in
@[simp]
theorem kummer_semilinear_lift
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ 3) (y : L) :
    cubicKummerSemilinear a sigma b hb
        (AdjoinRoot.of (cubicKummerPolynomial a) y) =
      AdjoinRoot.of (cubicKummerPolynomial a) (sigma y) := by
  simp [cubicKummerSemilinear]

omit [FiniteDimensional K L] in
@[simp]
theorem kummer_semilinear_root
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ 3) :
    cubicKummerSemilinear a sigma b hb
        (root (cubicKummerPolynomial a)) =
      algebraMap L (CubicKummerAdjoin a) (b : L) *
        root (cubicKummerPolynomial a) := by
  simp [cubicKummerSemilinear]

/-- The semilinear lift is an automorphism: it is an injective endomorphism
of the finite-dimensional `K`-vector space underlying the radical field. -/
noncomputable def kummerSemilinearLift
    (hirr : Irreducible (cubicKummerPolynomial a))
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ 3) :
    CubicKummerAdjoin a ≃ₐ[K] CubicKummerAdjoin a := by
  letI : Fact (Irreducible (cubicKummerPolynomial a)) := ⟨hirr⟩
  let f := cubicKummerSemilinear a sigma b hb
  apply AlgEquiv.ofBijective f
  have hinj : Function.Injective f := RingHom.injective f.toRingHom
  refine ⟨hinj, ?_⟩
  have hlinj : Function.Injective f.toLinearMap := hinj
  exact LinearMap.injective_iff_surjective.mp hlinj

@[simp]
theorem cubic_kummer_lift
    (hirr : Irreducible (cubicKummerPolynomial a))
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ 3) (y : L) :
    kummerSemilinearLift a hirr sigma b hb
        (AdjoinRoot.of (cubicKummerPolynomial a) y) =
      AdjoinRoot.of (cubicKummerPolynomial a) (sigma y) :=
  kummer_semilinear_lift a sigma b hb y

@[simp]
theorem cubic_kummer_semilinear
    (hirr : Irreducible (cubicKummerPolynomial a))
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ 3) (y : L) :
    kummerSemilinearLift a hirr sigma b hb
        (algebraMap L (CubicKummerAdjoin a) y) =
      algebraMap L (CubicKummerAdjoin a) (sigma y) := by
  simpa only [AdjoinRoot.algebraMap_eq] using
    cubic_kummer_lift a hirr sigma b hb y

@[simp]
theorem cubic_semilinear_root
    (hirr : Irreducible (cubicKummerPolynomial a))
    (sigma : Gal(L/K)) (b : Lˣ)
    (hb : sigma • a / a = b ^ 3) :
    kummerSemilinearLift a hirr sigma b hb
        (root (cubicKummerPolynomial a)) =
      algebraMap L (CubicKummerAdjoin a) (b : L) *
        root (cubicKummerPolynomial a) :=
  kummer_semilinear_root a sigma b hb

/-- The semilinear lift is insensitive to transport of its base
automorphism; the accompanying radical identity is proposition-valued. -/
theorem kummer_semilinear_congr
    (hirr : Irreducible (cubicKummerPolynomial a))
    {sigma tau : Gal(L/K)} (h : sigma = tau) (b : Lˣ)
    (hSigma : sigma • a / a = b ^ 3)
    (hTau : tau • a / a = b ^ 3) :
    kummerSemilinearLift a hirr sigma b hSigma =
      kummerSemilinearLift a hirr tau b hTau := by
  subst tau
  rfl

/-- A cubic unit acts on the radical field by multiplying the chosen root
and fixing the coefficient field. -/
noncomputable def kummerScalarAut
    (hirr : Irreducible (cubicKummerPolynomial a))
    (u : Lˣ) (hu : u ^ 3 = 1) :
    CubicKummerAdjoin a ≃ₐ[K] CubicKummerAdjoin a :=
  kummerSemilinearLift (K := K) (L := L) a hirr
    (1 : Gal(L/K)) u (by simp [hu])

@[simp]
theorem cubic_kummer_scalar
    (hirr : Irreducible (cubicKummerPolynomial a))
    (u : Lˣ) (hu : u ^ 3 = 1) (y : L) :
    kummerScalarAut (K := K) (L := L) a hirr u hu
        (AdjoinRoot.of (cubicKummerPolynomial a) y) =
      AdjoinRoot.of (cubicKummerPolynomial a) y := by
  simp [kummerScalarAut]

@[simp]
theorem kummer_scalar_aut
    (hirr : Irreducible (cubicKummerPolynomial a))
    (u : Lˣ) (hu : u ^ 3 = 1) (y : L) :
    kummerScalarAut (K := K) (L := L) a hirr u hu
        (algebraMap L (CubicKummerAdjoin a) y) =
      algebraMap L (CubicKummerAdjoin a) y := by
  simpa only [AdjoinRoot.algebraMap_eq] using
    cubic_kummer_scalar (K := K) (L := L) a hirr u hu y

@[simp]
theorem cubic_scalar_aut
    (hirr : Irreducible (cubicKummerPolynomial a))
    (u : Lˣ) (hu : u ^ 3 = 1) :
    kummerScalarAut (K := K) (L := L) a hirr u hu
        (root (cubicKummerPolynomial a)) =
      algebraMap L (CubicKummerAdjoin a) (u : L) *
        root (cubicKummerPolynomial a) := by
  simp [kummerScalarAut]

theorem cubic_kummer_aut
    (hirr : Irreducible (cubicKummerPolynomial a))
    (h1 : (1 : Lˣ) ^ 3 = 1) :
    kummerScalarAut (K := K) (L := L) a hirr 1 h1 = 1 := by
  apply AlgEquiv.coe_algHom_injective
  apply AdjoinRoot.algHom_ext'
  · ext y
    simp
  · simp [cubic_scalar_aut]

/-- The semilinear Kummer lifts multiply according to their factor-set
scalar. -/
theorem cubic_semilinear_lift
    (hirr : Irreducible (cubicKummerPolynomial a))
    (sigma tau : Gal(L/K)) (bSigma bTau bMul u : Lˣ)
    (hSigma : sigma • a / a = bSigma ^ 3)
    (hTau : tau • a / a = bTau ^ 3)
    (hMul : (sigma * tau) • a / a = bMul ^ 3)
    (hu : u ^ 3 = 1)
    (hc : sigma • bTau / bMul * bSigma = u) :
    kummerSemilinearLift a hirr sigma bSigma hSigma *
        kummerSemilinearLift a hirr tau bTau hTau =
      kummerScalarAut (K := K) (L := L) a hirr u hu *
        kummerSemilinearLift a hirr (sigma * tau) bMul hMul := by
  apply AlgEquiv.coe_algHom_injective
  apply AdjoinRoot.algHom_ext'
  · ext y
    simp
  · have hc' := hc
    change Units.map sigma.toRingEquiv.toMonoidHom bTau / bMul * bSigma = u at hc'
    simp only [div_eq_mul_inv] at hc'
    have hcoeff :
        Units.map sigma.toRingEquiv.toMonoidHom bTau * bSigma = u * bMul := by
      have hmul := congrArg (fun z : Lˣ => z * bMul) hc'
      calc
        Units.map sigma.toRingEquiv.toMonoidHom bTau * bSigma =
            (Units.map sigma.toRingEquiv.toMonoidHom bTau * bMul⁻¹ * bSigma) *
              bMul := by
                calc
                  Units.map sigma.toRingEquiv.toMonoidHom bTau * bSigma =
                      (bMul⁻¹ * bMul) *
                        (Units.map sigma.toRingEquiv.toMonoidHom bTau * bSigma) := by
                          simp
                  _ = (Units.map sigma.toRingEquiv.toMonoidHom bTau *
                        bMul⁻¹ * bSigma) * bMul := by ac_rfl
        _ = u * bMul := hmul
    change
      kummerSemilinearLift a hirr sigma bSigma hSigma
          (kummerSemilinearLift a hirr tau bTau hTau
            (root (cubicKummerPolynomial a))) =
        kummerScalarAut (K := K) (L := L) a hirr u hu
          (kummerSemilinearLift a hirr (sigma * tau) bMul hMul
            (root (cubicKummerPolynomial a)))
    rw [cubic_semilinear_root, map_mul,
      cubic_kummer_semilinear, cubic_semilinear_root,
      cubic_semilinear_root, map_mul,
      kummer_scalar_aut, cubic_scalar_aut]
    have hcoeff_val :
        sigma (bTau : L) * (bSigma : L) = (u : L) * (bMul : L) :=
      congrArg Units.val hcoeff
    calc
      algebraMap L (CubicKummerAdjoin a) (sigma (bTau : L)) *
            (algebraMap L (CubicKummerAdjoin a) (bSigma : L) *
              root (cubicKummerPolynomial a)) =
          algebraMap L (CubicKummerAdjoin a)
              (sigma (bTau : L) * (bSigma : L)) *
            root (cubicKummerPolynomial a) := by rw [map_mul, mul_assoc]
      _ = algebraMap L (CubicKummerAdjoin a)
              ((u : L) * (bMul : L)) * root (cubicKummerPolynomial a) := by
            rw [hcoeff_val]
      _ = algebraMap L (CubicKummerAdjoin a) (bMul : L) *
            (algebraMap L (CubicKummerAdjoin a) (u : L) *
              root (cubicKummerPolynomial a)) := by
            rw [map_mul]
            ac_rfl

/-- If the root scalars themselves satisfy the semilinear cocycle equation,
the corresponding Kummer lifts multiply strictly. -/
theorem kummer_semilinear_cocycle
    (hirr : Irreducible (cubicKummerPolynomial a))
    (sigma tau : Gal(L/K)) (bSigma bTau bMul : Lˣ)
    (hSigma : sigma • a / a = bSigma ^ 3)
    (hTau : tau • a / a = bTau ^ 3)
    (hMul : (sigma * tau) • a / a = bMul ^ 3)
    (hc : bMul = sigma • bTau * bSigma) :
    kummerSemilinearLift a hirr sigma bSigma hSigma *
        kummerSemilinearLift a hirr tau bTau hTau =
      kummerSemilinearLift a hirr (sigma * tau) bMul hMul := by
  have hc' : sigma • bTau / bMul * bSigma = (1 : Lˣ) := by
    rw [hc]
    rw [div_mul_cancel_left, inv_mul_cancel]
  have h := cubic_semilinear_lift a hirr sigma tau
    bSigma bTau bMul 1 hSigma hTau hMul (by simp) hc'
  rw [cubic_kummer_aut, one_mul] at h
  exact h

section CentralExtensionAction

variable {Q : Type v} {G : Type w} [Group Q] [Group G]

/-- The quotient component of the Kummer action, transported back to the
chosen Galois group. -/
noncomputable def kummerBaseHom
    (q : Q →* G) (galoisEquiv : Gal(L/K) ≃* G) :
    Q →* Gal(L/K) :=
  galoisEquiv.symm.toMonoidHom.comp q

/-- The radical scalar attached to an element of the abstract central
extension.  Its kernel coordinate supplies the cube-root-of-unity factor,
while `b` supplies the Hilbert-90 cochain factor. -/
noncomputable def extensionKummerScalar
    (q : Q →* G) (hq : Function.Surjective q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (b : Gal(L/K) → Lˣ) (e : Q) : Lˣ :=
  kernelToUnits (centralExtensionCoordinate q hq e) *
    b (kummerBaseHom q galoisEquiv e)

omit [FiniteDimensional K L] in
/-- The radical scalars satisfy the semilinear one-cocycle equation. -/
theorem extension_kummer_scalar
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      sigma • b tau / b (sigma * tau) * b sigma =
        kernelToUnits
          ((centralExtensionSet q hq hcentral)
            (galoisEquiv sigma, galoisEquiv tau)))
    (e f : Q) :
    extensionKummerScalar q hq galoisEquiv kernelToUnits b (e * f) =
      kummerBaseHom q galoisEquiv e •
          extensionKummerScalar q hq galoisEquiv kernelToUnits b f *
        extensionKummerScalar q hq galoisEquiv kernelToUnits b e := by
  let sigma : Gal(L/K) := kummerBaseHom q galoisEquiv e
  let tau : Gal(L/K) := kummerBaseHom q galoisEquiv f
  have hsigma : galoisEquiv sigma = q e := galoisEquiv.apply_symm_apply (q e)
  have htau : galoisEquiv tau = q f := galoisEquiv.apply_symm_apply (q f)
  have hst : kummerBaseHom q galoisEquiv (e * f) =
      sigma * tau :=
    map_mul (kummerBaseHom q galoisEquiv) e f
  have hfactor := hb sigma tau
  rw [hsigma, htau] at hfactor
  have hfactor' :
      kernelToUnits
          ((centralExtensionSet q hq hcentral) (q e, q f)) *
            b (sigma * tau) = sigma • b tau * b sigma := by
    calc
      kernelToUnits
            ((centralExtensionSet q hq hcentral) (q e, q f)) *
          b (sigma * tau) =
          (sigma • b tau / b (sigma * tau) * b sigma) *
            b (sigma * tau) := by rw [hfactor]
      _ = sigma • b tau * b sigma := by
        simp only [div_eq_mul_inv]
        calc
          (sigma • b tau * (b (sigma * tau))⁻¹ * b sigma) *
                b (sigma * tau) =
              ((b (sigma * tau))⁻¹ * b (sigma * tau)) *
                (sigma • b tau * b sigma) := by ac_rfl
          _ = sigma • b tau * b sigma := by simp
  have hfactorValue :
      kernelToUnits (centralExtensionValue q hq (q e) (q f)) *
          b (sigma * tau) = sigma • b tau * b sigma := by
    simpa [centralExtensionSet] using hfactor'
  change
    kernelToUnits (centralExtensionCoordinate q hq (e * f)) *
        b (kummerBaseHom q galoisEquiv (e * f)) =
      sigma •
          (kernelToUnits (centralExtensionCoordinate q hq f) * b tau) *
        (kernelToUnits (centralExtensionCoordinate q hq e) * b sigma)
  rw [central_extension_mul q hq hcentral e f, map_mul, map_mul,
    hst, smul_mul', hfixed]
  calc
    kernelToUnits (centralExtensionCoordinate q hq e) *
            kernelToUnits (centralExtensionCoordinate q hq f) *
            kernelToUnits (centralExtensionValue q hq (q e) (q f)) *
          b (sigma * tau) =
        kernelToUnits (centralExtensionCoordinate q hq e) *
          kernelToUnits (centralExtensionCoordinate q hq f) *
            (kernelToUnits (centralExtensionValue q hq (q e) (q f)) *
              b (sigma * tau)) := by group
    _ = kernelToUnits (centralExtensionCoordinate q hq e) *
          kernelToUnits (centralExtensionCoordinate q hq f) *
            (sigma • b tau * b sigma) := by rw [hfactorValue]
    _ = kernelToUnits (centralExtensionCoordinate q hq f) *
          sigma • b tau *
            (kernelToUnits (centralExtensionCoordinate q hq e) * b sigma) := by
          ac_rfl

omit [FiniteDimensional K L] in
/-- Every radical scalar has the cube required to extend its quotient
automorphism across the Kummer radical. -/
theorem kummer_scalar_cube
    (q : Q →* G) (hq : Function.Surjective q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (b : Gal(L/K) → Lˣ)
    (a : Lˣ)
    (hradical : ∀ sigma : Gal(L/K), sigma • a / a = b sigma ^ 3)
    (e : Q) :
    kummerBaseHom q galoisEquiv e • a / a =
      extensionKummerScalar q hq galoisEquiv kernelToUnits b e ^ 3 := by
  rw [hradical]
  simp only [extensionKummerScalar, mul_pow]
  rw [← map_pow, hkernel, map_one, one_mul]

/-- The Kummer automorphism attached to one element of the abstract central
extension. -/
noncomputable def centralKummerAction
    (q : Q →* G) (hq : Function.Surjective q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (b : Gal(L/K) → Lˣ) (a : Lˣ)
    (hradical : ∀ sigma : Gal(L/K), sigma • a / a = b sigma ^ 3)
    (hirr : Irreducible (cubicKummerPolynomial a))
    (e : Q) :
    CubicKummerAdjoin a ≃ₐ[K] CubicKummerAdjoin a :=
  kummerSemilinearLift a hirr
    (kummerBaseHom q galoisEquiv e)
    (extensionKummerScalar q hq galoisEquiv kernelToUnits b e)
    (kummer_scalar_cube q hq galoisEquiv kernelToUnits
      hkernel b a hradical e)

/-- The elementwise Kummer action respects multiplication in the abstract
central extension. -/
theorem central_kummer_action
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      sigma • b tau / b (sigma * tau) * b sigma =
        kernelToUnits
          ((centralExtensionSet q hq hcentral)
            (galoisEquiv sigma, galoisEquiv tau)))
    (a : Lˣ)
    (hradical : ∀ sigma : Gal(L/K), sigma • a / a = b sigma ^ 3)
    (hirr : Irreducible (cubicKummerPolynomial a))
    (e f : Q) :
    centralKummerAction q hq galoisEquiv kernelToUnits hkernel
        b a hradical hirr (e * f) =
      centralKummerAction q hq galoisEquiv kernelToUnits hkernel
          b a hradical hirr e *
        centralKummerAction q hq galoisEquiv kernelToUnits hkernel
          b a hradical hirr f := by
  let sigma := kummerBaseHom q galoisEquiv e
  let tau := kummerBaseHom q galoisEquiv f
  let bSigma := extensionKummerScalar q hq galoisEquiv kernelToUnits b e
  let bTau := extensionKummerScalar q hq galoisEquiv kernelToUnits b f
  let bMul := extensionKummerScalar q hq galoisEquiv kernelToUnits b (e * f)
  have hst : kummerBaseHom q galoisEquiv (e * f) =
      sigma * tau :=
    map_mul (kummerBaseHom q galoisEquiv) e f
  have hc : bMul = sigma • bTau * bSigma :=
    extension_kummer_scalar q hq hcentral galoisEquiv kernelToUnits
      hfixed b hb e f
  have hSigma : sigma • a / a = bSigma ^ 3 :=
    kummer_scalar_cube q hq galoisEquiv kernelToUnits
      hkernel b a hradical e
  have hTau : tau • a / a = bTau ^ 3 :=
    kummer_scalar_cube q hq galoisEquiv kernelToUnits
      hkernel b a hradical f
  have hEF : kummerBaseHom q galoisEquiv (e * f) • a / a =
      bMul ^ 3 :=
    kummer_scalar_cube q hq galoisEquiv kernelToUnits
      hkernel b a hradical (e * f)
  have hMul : (sigma * tau) • a / a = bMul ^ 3 := by
    rw [← map_mul (kummerBaseHom q galoisEquiv)]
    exact hEF
  have h := kummer_semilinear_cocycle a hirr sigma tau
    bSigma bTau bMul hSigma hTau hMul hc
  change
    kummerSemilinearLift a hirr
        (kummerBaseHom q galoisEquiv (e * f)) bMul hEF =
      kummerSemilinearLift a hirr sigma bSigma hSigma *
        kummerSemilinearLift a hirr tau bTau hTau
  exact (kummer_semilinear_congr a hirr hst bMul hEF hMul).trans h.symm

/-- The Kummer automorphisms form an action of the abstract central
extension. -/
noncomputable def kummerActionHom
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      sigma • b tau / b (sigma * tau) * b sigma =
        kernelToUnits
          ((centralExtensionSet q hq hcentral)
            (galoisEquiv sigma, galoisEquiv tau)))
    (a : Lˣ)
    (hradical : ∀ sigma : Gal(L/K), sigma • a / a = b sigma ^ 3)
    (hirr : Irreducible (cubicKummerPolynomial a)) :
    Q →* Gal(CubicKummerAdjoin a/K) where
  toFun := centralKummerAction q hq galoisEquiv kernelToUnits hkernel
    b a hradical hirr
  map_one' := by
    let x := centralKummerAction q hq galoisEquiv kernelToUnits hkernel
      b a hradical hirr 1
    have hx : x = x * x := by
      simpa [x] using central_kummer_action q hq hcentral galoisEquiv
        kernelToUnits hfixed hkernel b hb a hradical hirr 1 1
    apply mul_left_cancel (a := x)
    calc
      x * x = x := hx.symm
      _ = x * 1 := (mul_one x).symm
  map_mul' e f :=
    central_kummer_action q hq hcentral galoisEquiv kernelToUnits
      hfixed hkernel b hb a hradical hirr e f

@[simp]
theorem kummer_action_hom
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      sigma • b tau / b (sigma * tau) * b sigma =
        kernelToUnits
          ((centralExtensionSet q hq hcentral)
            (galoisEquiv sigma, galoisEquiv tau)))
    (a : Lˣ)
    (hradical : ∀ sigma : Gal(L/K), sigma • a / a = b sigma ^ 3)
    (hirr : Irreducible (cubicKummerPolynomial a)) (e : Q) :
    kummerActionHom q hq hcentral galoisEquiv kernelToUnits
        hfixed hkernel b hb a hradical hirr e =
      centralKummerAction q hq galoisEquiv kernelToUnits hkernel
        b a hradical hirr e :=
  rfl

omit [FiniteDimensional K L] in
/-- Normalization of the factor set forces its trivializing cochain to take
the value one at the identity. -/
theorem extension_kummer_cochain
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      sigma • b tau / b (sigma * tau) * b sigma =
        kernelToUnits
          ((centralExtensionSet q hq hcentral)
            (galoisEquiv sigma, galoisEquiv tau))) :
    b 1 = 1 := by
  simpa [centralExtensionSet, centralExtensionValue] using hb 1 1

@[simp]
theorem kummer_action_algebra
    (q : Q →* G) (hq : Function.Surjective q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (b : Gal(L/K) → Lˣ) (a : Lˣ)
    (hradical : ∀ sigma : Gal(L/K), sigma • a / a = b sigma ^ 3)
    (hirr : Irreducible (cubicKummerPolynomial a))
    (e : Q) (y : L) :
    centralKummerAction q hq galoisEquiv kernelToUnits hkernel
        b a hradical hirr e
        (algebraMap L (CubicKummerAdjoin a) y) =
      algebraMap L (CubicKummerAdjoin a)
        (kummerBaseHom q galoisEquiv e y) := by
  simp [centralKummerAction]

@[simp]
theorem kummer_action_root
    (q : Q →* G) (hq : Function.Surjective q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (b : Gal(L/K) → Lˣ) (a : Lˣ)
    (hradical : ∀ sigma : Gal(L/K), sigma • a / a = b sigma ^ 3)
    (hirr : Irreducible (cubicKummerPolynomial a))
    (e : Q) :
    centralKummerAction q hq galoisEquiv kernelToUnits hkernel
        b a hradical hirr e (root (cubicKummerPolynomial a)) =
      algebraMap L (CubicKummerAdjoin a)
          (extensionKummerScalar q hq galoisEquiv kernelToUnits b e : L) *
        root (cubicKummerPolynomial a) := by
  simp [centralKummerAction]

/-- If the kernel embedding into cube roots is injective, the Kummer action
faithfully realizes the prescribed abstract central extension. -/
theorem kummer_action_injective
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hkernelToUnits : Function.Injective kernelToUnits)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      sigma • b tau / b (sigma * tau) * b sigma =
        kernelToUnits
          ((centralExtensionSet q hq hcentral)
            (galoisEquiv sigma, galoisEquiv tau)))
    (a : Lˣ)
    (hradical : ∀ sigma : Gal(L/K), sigma • a / a = b sigma ^ 3)
    (hirr : Irreducible (cubicKummerPolynomial a)) :
    Function.Injective
      (kummerActionHom q hq hcentral galoisEquiv kernelToUnits
        hfixed hkernel b hb a hradical hirr) := by
  letI : Fact (Irreducible (cubicKummerPolynomial a)) := ⟨hirr⟩
  letI : Field (CubicKummerAdjoin a) := inferInstance
  let actionHom := kummerActionHom q hq hcentral galoisEquiv
    kernelToUnits hfixed hkernel b hb a hradical hirr
  have hb1 : b 1 = 1 :=
    extension_kummer_cochain q hq hcentral galoisEquiv kernelToUnits b hb
  have hker : ∀ e : Q, actionHom e = 1 → e = 1 := by
    intro e he
    have hbase : kummerBaseHom q galoisEquiv e = 1 := by
      apply AlgEquiv.ext
      intro y
      apply (algebraMap L (CubicKummerAdjoin a)).injective
      have happ := congrArg
        (fun phi : Gal(CubicKummerAdjoin a/K) =>
          phi (algebraMap L (CubicKummerAdjoin a) y)) he
      change
        centralKummerAction q hq galoisEquiv kernelToUnits hkernel
            b a hradical hirr e
              (algebraMap L (CubicKummerAdjoin a) y) =
          algebraMap L (CubicKummerAdjoin a) y at happ
      rw [kummer_action_algebra] at happ
      exact happ
    have hqe : q e = 1 := by
      have h := congrArg galoisEquiv hbase
      simpa [kummerBaseHom] using h
    have hrootne : root (cubicKummerPolynomial a) ≠ 0 := by
      simpa [cubicKummerPolynomial] using
        (root_X_pow_sub_C_ne_zero' (n := 3) (by norm_num : 0 < 3)
          (Units.ne_zero a))
    have hroot := congrArg
      (fun phi : Gal(CubicKummerAdjoin a/K) =>
        phi (root (cubicKummerPolynomial a))) he
    have hroot' :
        algebraMap L (CubicKummerAdjoin a)
            (extensionKummerScalar q hq galoisEquiv kernelToUnits b e : L) *
              root (cubicKummerPolynomial a) = root (cubicKummerPolynomial a) := by
      simpa [actionHom] using hroot
    have hscalarMap :
        algebraMap L (CubicKummerAdjoin a)
            (extensionKummerScalar q hq galoisEquiv kernelToUnits b e : L) = 1 := by
      apply mul_right_cancel₀ hrootne
      simpa using hroot'
    have hscalar :
        extensionKummerScalar q hq galoisEquiv kernelToUnits b e = 1 := by
      apply Units.ext
      apply (algebraMap L (CubicKummerAdjoin a)).injective
      simpa using hscalarMap
    have hcoordMap :
        kernelToUnits (centralExtensionCoordinate q hq e) = 1 := by
      simpa [extensionKummerScalar, hbase, hb1] using hscalar
    have hcoord : centralExtensionCoordinate q hq e = 1 := by
      apply hkernelToUnits
      simpa using hcoordMap
    have hcoordCoe := congrArg Subtype.val hcoord
    change e * (normalizedSurjInv q hq (q e))⁻¹ = 1 at hcoordCoe
    simpa [hqe] using hcoordCoe
  intro e f hef
  change actionHom e = actionHom f at hef
  have hz : e * f⁻¹ = 1 := by
    apply hker
    rw [map_mul, map_inv, hef, mul_inv_cancel]
  exact mul_inv_eq_one.mp hz

omit [FiniteDimensional K L] in
/-- If the Hilbert--90 radical is already a cube, its correcting cochain takes
values in the cubic kernel.  It therefore trivializes the original factor set
and gives a lift over the coefficient field itself. -/
theorem kummer_radical_cube
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hkernelToUnits : Function.Injective kernelToUnits)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (hroots : ∀ u : Lˣ, u ^ 3 = 1 → ∃ z : q.ker, kernelToUnits z = u)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      sigma • b tau / b (sigma * tau) * b sigma =
        kernelToUnits
          ((centralExtensionSet q hq hcentral)
            (galoisEquiv sigma, galoisEquiv tau)))
    (a c : Lˣ)
    (hradical : ∀ sigma : Gal(L/K), sigma • a / a = b sigma ^ 3)
    (hc : c ^ 3 = a) :
    ∃ lift : Gal(L/K) →* Q,
      q.comp lift = galoisEquiv.toMonoidHom := by
  letI : CommGroup q.ker :=
    centralExtensionComm q hcentral
  letI : MulDistribMulAction G q.ker :=
    trivialDistribAction G q.ker
  letI : MulDistribMulAction Gal(L/K) q.ker :=
    trivialDistribAction Gal(L/K) q.ker
  let d : Gal(L/K) → Lˣ := fun sigma => b sigma * c / (sigma • c)
  have hdCube (sigma : Gal(L/K)) : d sigma ^ 3 = 1 := by
    have hsigmaCube : (sigma • c) ^ 3 = sigma • a := by
      change
        (Units.map sigma.toRingEquiv.toMonoidHom c) ^ 3 =
          Units.map sigma.toRingEquiv.toMonoidHom a
      rw [← map_pow, hc]
    calc
      d sigma ^ 3 = b sigma ^ 3 * c ^ 3 / (sigma • c) ^ 3 := by
        simp only [d, mul_pow, div_pow]
      _ = (sigma • a / a) * a / (sigma • a) := by
        rw [← hradical, hc, hsigmaCube]
      _ = 1 := by
        calc
          (sigma • a) / a * a / (sigma • a) =
              (sigma • a) / (sigma • a) := by rw [div_mul_cancel]
          _ = 1 := by
            simp only [div_eq_mul_inv]
            exact mul_inv_cancel _
  choose z hz using fun sigma => hroots (d sigma) (hdCube sigma)
  have hbOne : b 1 = 1 := by
    have h := hb 1 1
    simpa using h
  have hzOne : z 1 = 1 := by
    apply hkernelToUnits
    rw [hz]
    have hone : (1 : Gal(L/K)) • c = c := one_smul _ c
    rw [show d 1 = c / c by simp only [d, hbOne, one_mul, hone]]
    simp only [div_eq_mul_inv, map_one]
    exact mul_inv_cancel c
  have hdFixed (sigma tau : Gal(L/K)) : sigma • d tau = d tau := by
    rw [← hz tau, hfixed]
  have hdRewrite (sigma tau : Gal(L/K)) :
      d tau = (sigma • b tau) * (sigma • c) / ((sigma * tau) • c) := by
    rw [← hdFixed sigma tau]
    change
      Units.map sigma.toRingEquiv.toMonoidHom
          (b tau * c / (tau • c)) =
        (sigma • b tau) * (sigma • c) / ((sigma * tau) • c)
    rw [_root_.map_div, map_mul]
    rw [mul_smul]
    rfl
  have hdCoboundary (sigma tau : Gal(L/K)) :
      d tau / d (sigma * tau) * d sigma =
        kernelToUnits
          ((centralExtensionSet q hq hcentral)
            (galoisEquiv sigma, galoisEquiv tau)) := by
    rw [hdRewrite sigma tau]
    rw [show d (sigma * tau) = b (sigma * tau) * c / ((sigma * tau) • c) by
      rfl]
    rw [show d sigma = b sigma * c / (sigma • c) by rfl]
    calc
      ((sigma • b tau) * (sigma • c) / ((sigma * tau) • c) /
            (b (sigma * tau) * c / ((sigma * tau) • c))) *
          (b sigma * c / (sigma • c)) =
          sigma • b tau / b (sigma * tau) * b sigma := by
            simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
            calc
              sigma • b tau * (sigma • c) * ((sigma * tau) • c)⁻¹ *
                    (((sigma * tau) • c) *
                      (c⁻¹ * (b (sigma * tau))⁻¹)) *
                    (b sigma * c * (sigma • c)⁻¹) =
                  sigma • b tau * (sigma • c) * c⁻¹ *
                    (b (sigma * tau))⁻¹ * b sigma * c *
                      (sigma • c)⁻¹ := by group
              _ =
                  sigma • b tau *
                    (((sigma • c) * (sigma • c)⁻¹) *
                      (c⁻¹ * c) * ((b (sigma * tau))⁻¹ * b sigma)) := by
                        ac_rfl
              _ = sigma • b tau * (b (sigma * tau))⁻¹ * b sigma := by
                simp only [mul_inv_cancel, inv_mul_cancel, mul_one, one_mul]
                group
      _ = kernelToUnits
          ((centralExtensionSet q hq hcentral)
            (galoisEquiv sigma, galoisEquiv tau)) := hb sigma tau
  have hzCoboundary (sigma tau : Gal(L/K)) :
      z tau / z (sigma * tau) * z sigma =
        (centralExtensionSet q hq hcentral)
          (galoisEquiv sigma, galoisEquiv tau) := by
    apply hkernelToUnits
    rw [map_mul, _root_.map_div, hz, hz, hz]
    exact hdCoboundary sigma tau
  let cH : CFSet Gal(L/K) q.ker :=
    { toFun := fun p =>
        (centralExtensionSet q hq hcentral)
          (galoisEquiv p.1, galoisEquiv p.2)
      map_one_fst := by intro sigma; simp
      map_one_snd := by intro sigma; simp
      cocycle := by
        intro sigma tau rho
        simpa only [map_mul] using
          (centralExtensionSet q hq hcentral).cocycle
            (galoisEquiv sigma) (galoisEquiv tau) (galoisEquiv rho) }
  have hcH : cH.IsTrivial := by
    refine ⟨fun sigma => (z sigma)⁻¹, ?_, ?_⟩
    · simp [hzOne]
    · intro sigma tau
      have h := hzCoboundary sigma tau
      change (z (sigma * tau))⁻¹ =
        (z sigma)⁻¹ * (z tau)⁻¹ *
          (centralExtensionSet q hq hcentral)
            (galoisEquiv sigma, galoisEquiv tau)
      rw [← h]
      simp only [div_eq_mul_inv]
      symm
      calc
        (z sigma)⁻¹ * (z tau)⁻¹ *
              (z tau * (z (sigma * tau))⁻¹ * z sigma) =
            (z sigma)⁻¹ * (z tau)⁻¹ *
              (z tau * (z (sigma * tau))⁻¹) * z sigma := by group
        _ =
            (((z sigma)⁻¹ * z sigma) * ((z tau)⁻¹ * z tau)) *
              (z (sigma * tau))⁻¹ := by ac_rfl
        _ = (z (sigma * tau))⁻¹ := by simp
  have hzero :
      MHTwo.restrictionHom galoisEquiv.toMonoidHom
          (fun _ _ => rfl)
          (extensionObstructionClass q hq hcentral) = 1 := by
    change MHTwo.mk
      (NMCocycl₂.restrict galoisEquiv.toMonoidHom
        (fun _ _ => rfl)
        ((centralExtensionSet q hq hcentral).normalizedMulCocycle
          (fun _ _ => rfl))) = 1
    exact
      (CFSet.trivial_multiplicative_h cH
        (fun _ _ => rfl)).1 hcH
  exact lift_obstruction_restrict
    q hq hcentral galoisEquiv.toMonoidHom hzero

/-- An injective order-three coefficient group fills the full group of cubic
roots of unity as soon as the coefficient field contains a primitive one. -/
theorem cubic_cube_roots
    {C : Type v} [Group C] [Finite C]
    (hcard : Nat.card C = 3)
    (kernelToUnits : C →* Lˣ)
    (hkernelToUnits : Function.Injective kernelToUnits)
    (hkernel : ∀ z : C, z ^ 3 = 1)
    (zeta : L) (hzeta : IsPrimitiveRoot zeta 3) :
    ∀ u : Lˣ, u ^ 3 = 1 → ∃ z : C, kernelToUnits z = u := by
  let toRoots : C →* rootsOfUnity 3 L :=
    { toFun := fun z =>
        ⟨kernelToUnits z, (mem_rootsOfUnity 3 (kernelToUnits z)).2 (by
          rw [← map_pow, hkernel, map_one])⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp }
  have htoRootsInjective : Function.Injective toRoots := by
    intro x y hxy
    apply hkernelToUnits
    exact congrArg Subtype.val hxy
  letI := Fintype.ofFinite C
  have hcardC : Fintype.card C = 3 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hcardRoots : Fintype.card (rootsOfUnity 3 L) = 3 :=
    hzeta.card_rootsOfUnity
  have htoRootsSurjective : Function.Surjective toRoots :=
    (Fintype.bijective_iff_injective_and_card toRoots).2
      ⟨htoRootsInjective, hcardC.trans hcardRoots.symm⟩ |>.2
  intro u hu
  obtain ⟨z, hz⟩ := htoRootsSurjective
    ⟨u, (mem_rootsOfUnity 3 u).2 hu⟩
  exact ⟨z, congrArg Subtype.val hz⟩

/-- In the irreducible-radical case, the faithful Kummer action has the full
degree predicted by the central extension.  Consequently the radical field
is Galois over `K`, and the action identifies its Galois group with `Q`. -/
theorem kummer_action_bijective
    [Finite Q] [Finite G] [IsGalois K L]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (hkernelCard : Nat.card q.ker = 3)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hkernelToUnits : Function.Injective kernelToUnits)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      sigma • b tau / b (sigma * tau) * b sigma =
        kernelToUnits
          ((centralExtensionSet q hq hcentral)
            (galoisEquiv sigma, galoisEquiv tau)))
    (a : Lˣ)
    (hradical : ∀ sigma : Gal(L/K), sigma • a / a = b sigma ^ 3)
    (hirr : Irreducible (cubicKummerPolynomial a)) :
    letI : Fact (Irreducible (cubicKummerPolynomial a)) := ⟨hirr⟩
    ∃ _hGal : IsGalois K (CubicKummerAdjoin a),
      Function.Bijective
        (kummerActionHom q hq hcentral galoisEquiv kernelToUnits
          hfixed hkernel b hb a hradical hirr) := by
  letI : Fact (Irreducible (cubicKummerPolynomial a)) := ⟨hirr⟩
  letI : Field (CubicKummerAdjoin a) := inferInstance
  let actionHom := kummerActionHom q hq hcentral galoisEquiv
    kernelToUnits hfixed hkernel b hb a hradical hirr
  have hactionInjective : Function.Injective actionHom :=
    kummer_action_injective q hq hcentral galoisEquiv
      kernelToUnits hkernelToUnits hfixed hkernel b hb a hradical hirr
  have hindex : q.ker.index = Nat.card G := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hq]
    simp
  have hcardQ : Nat.card Q = 3 * Nat.card G := by
    calc
      Nat.card Q = Nat.card q.ker * q.ker.index := q.ker.card_mul_index.symm
      _ = 3 * Nat.card G := by rw [hkernelCard, hindex]
  have hfinrankLK : Module.finrank K L = Nat.card G := by
    calc
      Module.finrank K L = Nat.card Gal(L/K) :=
        (IsGalois.card_aut_eq_finrank K L).symm
      _ = Nat.card G := Nat.card_congr galoisEquiv.toEquiv
  have hfinrankNL : Module.finrank L (CubicKummerAdjoin a) = 3 := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank]
    simp [cubicKummerPolynomial]
  have hfinrankKN :
      Module.finrank K (CubicKummerAdjoin a) = 3 * Nat.card G := by
    calc
      Module.finrank K (CubicKummerAdjoin a) =
          Module.finrank K L * Module.finrank L (CubicKummerAdjoin a) :=
        (Module.finrank_mul_finrank K L (CubicKummerAdjoin a)).symm
      _ = Nat.card G * 3 := by rw [hfinrankLK, hfinrankNL]
      _ = 3 * Nat.card G := Nat.mul_comm _ _
  have hcardQFinrank :
      Nat.card Q = Module.finrank K (CubicKummerAdjoin a) :=
    hcardQ.trans hfinrankKN.symm
  have hQleAut : Nat.card Q ≤ Nat.card Gal(CubicKummerAdjoin a/K) :=
    Nat.card_le_card_of_injective actionHom hactionInjective
  have hAutLeFinrank :
      Nat.card Gal(CubicKummerAdjoin a/K) ≤
        Module.finrank K (CubicKummerAdjoin a) := by
    rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  have hcardAut :
      Nat.card Gal(CubicKummerAdjoin a/K) =
        Module.finrank K (CubicKummerAdjoin a) := by
    apply Nat.le_antisymm hAutLeFinrank
    rw [← hcardQFinrank]
    exact hQleAut
  let hGal : IsGalois K (CubicKummerAdjoin a) :=
    IsGalois.of_card_aut_eq_finrank K (CubicKummerAdjoin a) hcardAut
  letI : IsGalois K (CubicKummerAdjoin a) := hGal
  letI := Fintype.ofFinite Q
  letI := Fintype.ofFinite Gal(CubicKummerAdjoin a/K)
  have hactionSurjective : Function.Surjective actionHom :=
    (Fintype.bijective_iff_injective_and_card actionHom).2
      ⟨hactionInjective, by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
        exact hcardQFinrank.trans hcardAut.symm⟩ |>.2
  exact ⟨hGal, hactionInjective, hactionSurjective⟩

/-- A bijective Kummer action gives the weak solution in the direction used by
embedding problems.  The accompanying base homomorphism is characterized by
the actual action of every automorphism on the embedded coefficient field. -/
theorem bijective_weak_solution
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (b : Gal(L/K) → Lˣ)
    (hb : ∀ sigma tau : Gal(L/K),
      sigma • b tau / b (sigma * tau) * b sigma =
        kernelToUnits
          ((centralExtensionSet q hq hcentral)
            (galoisEquiv sigma, galoisEquiv tau)))
    (a : Lˣ)
    (hradical : ∀ sigma : Gal(L/K), sigma • a / a = b sigma ^ 3)
    (hirr : Irreducible (cubicKummerPolynomial a))
    (hbij : Function.Bijective
      (kummerActionHom q hq hcentral galoisEquiv kernelToUnits
        hfixed hkernel b hb a hradical hirr)) :
    letI : Fact (Irreducible (cubicKummerPolynomial a)) := ⟨hirr⟩
    ∃ (lift : Gal(CubicKummerAdjoin a/K) →* Q)
        (baseHom : Gal(CubicKummerAdjoin a/K) →* Gal(L/K)),
      q.comp lift = galoisEquiv.toMonoidHom.comp baseHom ∧
        ∀ sigma : Gal(CubicKummerAdjoin a/K), ∀ y : L,
          sigma (algebraMap L (CubicKummerAdjoin a) y) =
            algebraMap L (CubicKummerAdjoin a) (baseHom sigma y) := by
  let actionHom := kummerActionHom q hq hcentral galoisEquiv
    kernelToUnits hfixed hkernel b hb a hradical hirr
  let actionEquiv : Q ≃* Gal(CubicKummerAdjoin a/K) :=
    MulEquiv.ofBijective actionHom hbij
  let lift : Gal(CubicKummerAdjoin a/K) →* Q :=
    actionEquiv.symm.toMonoidHom
  let baseHom : Gal(CubicKummerAdjoin a/K) →* Gal(L/K) :=
    (kummerBaseHom q galoisEquiv).comp lift
  refine ⟨lift, baseHom, ?_, ?_⟩
  · ext sigma
    simp [lift, baseHom, kummerBaseHom]
  · intro sigma y
    have hinverse : actionHom (lift sigma) = sigma := by
      exact actionEquiv.apply_symm_apply sigma
    have happ := congrArg
      (fun phi : Gal(CubicKummerAdjoin a/K) =>
        phi (algebraMap L (CubicKummerAdjoin a) y)) hinverse
    change
      centralKummerAction q hq galoisEquiv kernelToUnits hkernel
          b a hradical hirr (lift sigma)
            (algebraMap L (CubicKummerAdjoin a) y) =
        sigma (algebraMap L (CubicKummerAdjoin a) y) at happ
    rw [kummer_action_algebra] at happ
    exact happ.symm

/-- Vanishing of the coefficient-field-valued central obstruction has exactly
the two Kummer outcomes: either the radical is a cube and the problem already
has a lift over `L`, or adjoining its cube root realizes the entire central
extension as a Galois group over `K`. -/
theorem central_kummer_solution
    [Finite Q] [Finite G] [IsGalois K L]
    (q : Q →* G) (hq : Function.Surjective q)
    (hcentral : q.ker ≤ Subgroup.center Q)
    (hkernelCard : Nat.card q.ker = 3)
    (galoisEquiv : Gal(L/K) ≃* G)
    (kernelToUnits : q.ker →* Lˣ)
    (hkernelToUnits : Function.Injective kernelToUnits)
    (hfixed : ∀ sigma : Gal(L/K), ∀ z : q.ker,
      sigma • kernelToUnits z = kernelToUnits z)
    (hkernel : ∀ z : q.ker, z ^ 3 = 1)
    (zeta : L) (hzeta : IsPrimitiveRoot zeta 3)
    (hzero : centralExtensionClass q hq hcentral galoisEquiv
      kernelToUnits hfixed = 1) :
    (∃ lift : Gal(L/K) →* Q,
        q.comp lift = galoisEquiv.toMonoidHom) ∨
      ∃ (b : Gal(L/K) → Lˣ) (a : Lˣ)
          (hb : ∀ sigma tau : Gal(L/K),
            sigma • b tau / b (sigma * tau) * b sigma =
              kernelToUnits
                ((centralExtensionSet q hq hcentral)
                  (galoisEquiv sigma, galoisEquiv tau)))
          (hradical : ∀ sigma : Gal(L/K), sigma • a / a = b sigma ^ 3)
          (hirr : Irreducible (cubicKummerPolynomial a)),
        letI : Fact (Irreducible (cubicKummerPolynomial a)) := ⟨hirr⟩
        ∃ _hGal : IsGalois K (CubicKummerAdjoin a),
          Function.Bijective
            (kummerActionHom q hq hcentral galoisEquiv
              kernelToUnits hfixed hkernel b hb a hradical hirr) := by
  obtain ⟨b, hb, a, hradical⟩ :=
    central_kummer_data q hq hcentral
      galoisEquiv kernelToUnits hfixed hkernel hzero
  by_cases hirr : Irreducible (cubicKummerPolynomial a)
  · right
    refine ⟨b, a, hb, hradical, hirr, ?_⟩
    exact kummer_action_bijective q hq hcentral
      hkernelCard galoisEquiv kernelToUnits hkernelToUnits hfixed hkernel
      b hb a hradical hirr
  · left
    have hnotPower : ¬∀ c : L, c ^ 3 ≠ (a : L) := by
      intro hpower
      apply hirr
      rw [cubicKummerPolynomial]
      exact X_pow_sub_C_irreducible_of_prime (by norm_num) hpower
    obtain ⟨c, hc⟩ : ∃ c : L, c ^ 3 = (a : L) := by
      simpa only [not_forall, not_ne_iff] using hnotPower
    have hc0 : c ≠ 0 := by
      intro hcZero
      have haZero : (a : L) = 0 := by simpa [hcZero] using hc.symm
      exact a.ne_zero haZero
    let cUnit : Lˣ := Units.mk0 c hc0
    have hcUnit : cUnit ^ 3 = a := by
      apply Units.ext
      exact hc
    let hroots := cubic_cube_roots
      hkernelCard kernelToUnits hkernelToUnits hkernel zeta hzeta
    exact kummer_radical_cube q hq hcentral
      galoisEquiv kernelToUnits hkernelToUnits hfixed hroots b hb a cUnit
      hradical hcUnit

end CentralExtensionAction

end

end TBluepr
end Towers

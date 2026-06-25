import Submission.ClassField.LubinTate.PadicRootAmbient
import Submission.ClassField.LubinTate.RootFieldAdic
import Submission.ClassField.LubinTate.PadicGaloisAction

/-!
# The semilinear action on the cyclotomic Witt-root algebra

This file evaluates the finite cyclotomic Lubin--Tate module in the complete
root ideal constructed in `PadicCyclotomicWittRootAmbient` and transports its
exact quotient-unit orbit to the Witt coefficient ring.
-/

namespace Submission.CField.LTate

open Polynomial PowerSeries
open Submission.CField.FGroups

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]

local instance padicCyclotomicDatumResidueFintype :
    Fintype (ℤ_[p] ⧸ Ideal.span {(cyclotomicLubinDatum p).pi}) := by
  change Fintype (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})
  infer_instance

private abbrev W := WittVector p k
private abbrev B (n : ℕ) := PadicWittRing p k n
private abbrev C (n : ℕ) := FractionRing (B p k n)

/-- The coefficient map from `Z_p` to the finite Witt-root algebra. -/
def padicWittRing (n : ℕ) : ℤ_[p] →+* B p k n :=
  (algebraMap (W p k) (B p k n)).comp (padicIntWitt p k)

omit [IsAlgClosed k] in
theorem padic_witt_injective (n : ℕ) :
    Function.Injective (padicWittRing p k n) := by
  have hW : Function.Injective
      (algebraMap (W p k) (B p k n)) := by
    rw [AdjoinRoot.algebraMap_eq]
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [degree_eq_natDegree
      (witt_reduced_monic p k n).ne_zero]
    norm_num
    rw [padicWittReduced]
    rw [(reduced_iterate_monic
      (padic_lubin_monic p)
      (padic_cyclotomic_lubin p)
      (by rw [padic_lubin_degree]
          exact (Fact.out : p.Prime).ne_zero) n).natDegree_map]
    rw [reduced_iterate_degree,
      padic_lubin_degree]
    exact Nat.ne_of_gt <| Nat.mul_pos
      (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
      (pow_pos (Fact.out : p.Prime).pos n)
  intro a b hab
  apply int_witt_injective p k
  apply hW
  exact hab

/-- The induced embedding of `Q_p` into the fraction field of the root
algebra. -/
def wittRootFraction (n : ℕ) : ℚ_[p] →+* C p k n :=
  IsFractionRing.lift (A := ℤ_[p]) (K := ℚ_[p]) (L := C p k n)
    (g := (algebraMap (B p k n) (C p k n)).comp
      (padicWittRing p k n))
    ((IsFractionRing.injective (B p k n) (C p k n)).comp
      (padic_witt_injective p k n))

@[simp]
theorem root_fraction_algebra (n : ℕ) (a : ℤ_[p]) :
    wittRootFraction p k n (algebraMap ℤ_[p] ℚ_[p] a) =
      algebraMap (B p k n) (C p k n) (padicWittRing p k n a) :=
  by
    unfold wittRootFraction
    exact IsFractionRing.lift_algebraMap
      (A := ℤ_[p]) (K := ℚ_[p]) (L := C p k n) _ a

/-- The integral Witt root satisfies the scalar-extended reduced
cyclotomic polynomial in the common fraction field. -/
theorem cyclotomic_witt_root₂_reduced_eq_zero (n : ℕ) :
    Polynomial.eval₂ (wittRootFraction p k n)
      (algebraMap (B p k n) (C p k n)
        (cyclotomicWittRoot p k n))
      ((reducedLubinIterate
        (cyclotomicLubinDatum p).f n).map
          (algebraMap ℤ_[p] ℚ_[p])) = 0 := by
  let D := cyclotomicLubinDatum p
  let x : C p k n := algebraMap (B p k n) (C p k n)
    (cyclotomicWittRoot p k n)
  change Polynomial.eval₂ (wittRootFraction p k n) x
    ((reducedLubinIterate D.f n).map (algebraMap ℤ_[p] ℚ_[p])) = 0
  rw [Polynomial.eval₂_map]
  have hcoeff :
      (wittRootFraction p k n).comp (algebraMap ℤ_[p] ℚ_[p]) =
        (algebraMap (B p k n) (C p k n)).comp
          (padicWittRing p k n) := by
    ext a
    exact root_fraction_algebra p k n a
  rw [hcoeff]
  rw [← Polynomial.hom_eval₂]
  change algebraMap (B p k n) (C p k n)
      (Polynomial.eval₂ (padicWittRing p k n)
        (cyclotomicWittRoot p k n)
        (reducedLubinIterate D.f n)) = 0
  rw [show Polynomial.eval₂ (padicWittRing p k n)
      (cyclotomicWittRoot p k n)
      (reducedLubinIterate D.f n) = 0 by
    change Polynomial.eval₂
      ((algebraMap (W p k) (B p k n)).comp (padicIntWitt p k))
      (AdjoinRoot.root (padicWittReduced p k n))
      (reducedLubinIterate D.f n) = 0
    rw [← Polynomial.eval₂_map]
    exact AdjoinRoot.eval₂_root _]
  exact map_zero _

/-- The distinguished root field embeds into the common Witt fraction
field, carrying its distinguished root to the integral Witt root. -/
def padicCyclotomicFraction (n : ℕ) :
    (cyclotomicLubinDatum p).RootField ℚ_[p] n →+* C p k n :=
  AdjoinRoot.lift (wittRootFraction p k n)
    (algebraMap (B p k n) (C p k n)
      (cyclotomicWittRoot p k n))
    (cyclotomic_witt_root₂_reduced_eq_zero p k n)

@[simp]
theorem padic_cyclotomic_fraction (n : ℕ) :
    padicCyclotomicFraction p k n
        ((cyclotomicLubinDatum p).root ℚ_[p] n) =
      algebraMap (B p k n) (C p k n)
        (cyclotomicWittRoot p k n) := by
  exact AdjoinRoot.lift_root
    (f := (cyclotomicLubinDatum p).reducedPolynomial ℚ_[p] n)
    (h := cyclotomic_witt_root₂_reduced_eq_zero p k n)

/-- The distinguished integral Witt root as a point of the base-changed
cyclotomic Lubin--Tate formal group. -/
def padicCyclotomicPoint (n : ℕ) :
    let D := cyclotomicLubinDatum p
    let hI := padic_cyclotomic_adic p k n
    RelativeLubinPoints hI (padicWittRing p k n)
      D.pi D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit
      (padic_int_field p) (D.f : PowerSeries ℤ_[p])
      D.lubin_tate_card := by
  dsimp only
  let D := cyclotomicLubinDatum p
  let hI := padic_cyclotomic_adic p k n
  exact FGLaw.APts.ofIdeal hI _
    ⟨cyclotomicWittRoot p k n,
      Ideal.mem_span_singleton_self _⟩

@[simp]
theorem padic_witt_point (n : ℕ) :
    let D := cyclotomicLubinDatum p
    let hI := padic_cyclotomic_adic p k n
    ((FGLaw.APts.toIdeal hI
      ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
        D.pi_irreducible.not_isUnit (padic_int_field p)
        (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map
          (padicWittRing p k n))
      (padicCyclotomicPoint p k n) :
        Ideal.span {cyclotomicWittRoot p k n}) : B p k n) =
      cyclotomicWittRoot p k n := by
  rfl

set_option maxHeartbeats 3000000 in
-- Exact torsion computation unfolds the complete relative point module.
/-- The Witt root has exact cyclotomic Lubin--Tate level `n + 1`. -/
theorem witt_point_torsion (n : ℕ) :
    let D := cyclotomicLubinDatum p
    let hI := padic_cyclotomic_adic p k n
    Ideal.torsionOf ℤ_[p]
      (RelativeLubinPoints hI (padicWittRing p k n)
        D.pi D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit
        (padic_int_field p) (D.f : PowerSeries ℤ_[p])
        D.lubin_tate_card)
      (padicCyclotomicPoint p k n) =
        Ideal.span {D.pi ^ (n + 1)} := by
  dsimp only
  let D := cyclotomicLubinDatum p
  let hI := padic_cyclotomic_adic p k n
  apply D.torsion_relative_point ℚ_[p]
    hI (padicWittRing p k n)
    (padic_int_field p) n
    (padicCyclotomicPoint p k n)
    (algebraMap (B p k n) (C p k n))
    (IsFractionRing.injective (B p k n) (C p k n))
    (padicCyclotomicFraction p k n)
  · ext a
    change algebraMap (B p k n) (C p k n)
        (padicWittRing p k n a) =
      padicCyclotomicFraction p k n
        (algebraMap ℚ_[p]
          ((cyclotomicLubinDatum p).RootField ℚ_[p] n)
          (algebraMap ℤ_[p] ℚ_[p] a))
    rw [show padicCyclotomicFraction p k n
        (algebraMap ℚ_[p]
          ((cyclotomicLubinDatum p).RootField ℚ_[p] n)
          (algebraMap ℤ_[p] ℚ_[p] a)) =
        wittRootFraction p k n (algebraMap ℤ_[p] ℚ_[p] a) by
      exact AdjoinRoot.lift_of
        (f := (cyclotomicLubinDatum p).reducedPolynomial ℚ_[p] n)
        (h := cyclotomic_witt_root₂_reduced_eq_zero p k n)]
    exact (root_fraction_algebra p k n a).symm
  · rw [padic_witt_point,
      padic_cyclotomic_fraction]

/-- Scalar multiplication of the distinguished Witt root by a `p`-adic
unit. -/
def padicWittPoint (n : ℕ) (u : ℤ_[p]ˣ) :
    let D := cyclotomicLubinDatum p
    let hI := padic_cyclotomic_adic p k n
    RelativeLubinPoints hI (padicWittRing p k n)
      D.pi D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit
      (padic_int_field p) (D.f : PowerSeries ℤ_[p])
      D.lubin_tate_card := by
  dsimp only
  exact (u : ℤ_[p]) • padicCyclotomicPoint p k n

set_option maxHeartbeats 2000000 in
-- Unfolding the cyclic quotient coordinate and the adic module action is expensive.
/-- Every unit translate has the same exact torsion level. -/
theorem padic_point_torsion
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let D := cyclotomicLubinDatum p
    let hI := padic_cyclotomic_adic p k n
    Ideal.torsionOf ℤ_[p]
      (RelativeLubinPoints hI (padicWittRing p k n)
        D.pi D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit
        (padic_int_field p) (D.f : PowerSeries ℤ_[p])
        D.lubin_tate_card)
      (padicWittPoint p k n u) =
        Ideal.span {D.pi ^ (n + 1)} := by
  dsimp only
  let D := cyclotomicLubinDatum p
  let hI := padic_cyclotomic_adic p k n
  let y := padicCyclotomicPoint p k n
  let hy := witt_point_torsion p k n
  let q : (ℤ_[p] ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ :=
    Units.map (Ideal.Quotient.mk _).toMonoidHom u
  have horbit :
      orbitEmbeddingTorsion y hy q =
        (u : ℤ_[p]) • y := by
    apply torsion_smul_mk
    rfl
  change Ideal.torsionOf ℤ_[p] _ ((u : ℤ_[p]) • y) = _
  rw [← horbit]
  exact torsion_orbit_embedding y hy q

/-- A unit translate of the root is again a root of the reduced cyclotomic
level polynomial. -/
theorem padic_point_reduced
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let D := cyclotomicLubinDatum p
    let hI := padic_cyclotomic_adic p k n
    Polynomial.eval₂ (padicWittRing p k n)
      (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit (padic_int_field p)
          (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map
            (padicWittRing p k n))
        (padicWittPoint p k n u) : B p k n)
      (reducedLubinIterate D.f n) = 0 := by
  dsimp only
  let D := cyclotomicLubinDatum p
  let hI := padic_cyclotomic_adic p k n
  exact D.eval₂_reducedLubinTateIterate_eq_zero_of_torsionOf_eq
    hI (padicWittRing p k n)
    (padic_int_field p) n
    (padicWittPoint p k n u)
    (padic_point_torsion p k n u)

/-- The underlying Witt-algebra element of a unit translate of the
distinguished cyclotomic root. -/
def padicWittValue (n : ℕ) (u : ℤ_[p]ˣ) : B p k n :=
  let D := cyclotomicLubinDatum p
  let hI := padic_cyclotomic_adic p k n
  FGLaw.APts.toIdeal hI
    ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
      D.pi_irreducible.not_isUnit (padic_int_field p)
      (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map
        (padicWittRing p k n))
    (padicWittPoint p k n u)

@[simp]
theorem padic_witt_one (n : ℕ) :
    padicWittValue p k n 1 =
      cyclotomicWittRoot p k n := by
  have hpoint : padicWittPoint p k n 1 =
      padicCyclotomicPoint p k n := by
    change (1 : ℤ_[p]) • padicCyclotomicPoint p k n = _
    exact one_smul _ _
  rw [padicWittValue, hpoint]
  exact padic_witt_point p k n

omit [IsAlgClosed k] in
/-- Witt Frobenius fixes the scalar-extended cyclotomic reduced polynomial. -/
theorem witt_reduced_frobenius (n : ℕ) :
    (padicWittReduced p k n).map
        WittVector.frobenius =
      padicWittReduced p k n := by
  apply Polynomial.ext
  intro i
  simp only [padicWittReduced,
    Polynomial.coeff_map]
  exact frobenius_int_witt p k
    ((reducedLubinIterate
      (padicCyclotomicLubin p) n).coeff i)

/-- The inverse-unit root is a root after applying Witt Frobenius to the
coefficients. -/
theorem padic_witt_eval₂_frobenius_eq_zero
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let f := padicWittReduced p k n
    Polynomial.eval₂ ((AdjoinRoot.of f).comp WittVector.frobenius)
      (padicWittValue p k n u⁻¹) f = 0 := by
  dsimp only
  let f := padicWittReduced p k n
  let y := padicWittValue p k n u⁻¹
  rw [← Polynomial.eval_map]
  rw [← Polynomial.map_map]
  rw [witt_reduced_frobenius p k n]
  rw [Polynomial.eval_map]
  change Polynomial.eval₂ (AdjoinRoot.of f) y
    ((reducedLubinIterate
      (cyclotomicLubinDatum p).f n).map
        (padicIntWitt p k)) = 0
  rw [Polynomial.eval₂_map]
  change Polynomial.eval₂ (padicWittRing p k n) y
    (reducedLubinIterate
      (cyclotomicLubinDatum p).f n) = 0
  exact padic_point_reduced p k n u⁻¹

/-- The semilinear endomorphism of the finite root algebra: Witt Frobenius
on coefficients and the inverse-unit Lubin--Tate orbit on the root. -/
def wittFrobeniusLift (n : ℕ) (u : ℤ_[p]ˣ) :
    B p k n →+* B p k n :=
  let f := padicWittReduced p k n
  let y := padicWittValue p k n u⁻¹
  AdjoinRoot.lift ((AdjoinRoot.of f).comp WittVector.frobenius) y
    (padic_witt_eval₂_frobenius_eq_zero p k n u)

@[simp]
theorem padic_witt_coeff
    (n : ℕ) (u : ℤ_[p]ˣ) (a : W p k) :
    wittFrobeniusLift p k n u
        (algebraMap (W p k) (B p k n) a) =
      algebraMap (W p k) (B p k n) (WittVector.frobenius a) := by
  exact AdjoinRoot.lift_of
    (f := padicWittReduced p k n)
    (h := padic_witt_eval₂_frobenius_eq_zero p k n u)

@[simp]
theorem padic_frobenius_root
    (n : ℕ) (u : ℤ_[p]ˣ) :
    wittFrobeniusLift p k n u
        (cyclotomicWittRoot p k n) =
      padicWittValue p k n u⁻¹ := by
  exact AdjoinRoot.lift_root
    (f := padicWittReduced p k n)
    (h := padic_witt_eval₂_frobenius_eq_zero p k n u)

/-- A unit translate is still contained in the distinguished root ideal. -/
theorem padic_cyclotomic_witt
    (n : ℕ) (u : ℤ_[p]ˣ) :
    padicWittValue p k n u ∈
      Ideal.span {cyclotomicWittRoot p k n} := by
  unfold padicWittValue
  exact (FGLaw.APts.toIdeal
    (padic_cyclotomic_adic p k n) _
    (padicWittPoint p k n u)).property

/-- An additive homomorphism preserving an ideal of definition is
continuous for the corresponding adic topology. -/
theorem continuous_adic_ideal
    {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [IsTopologicalRing R]
    (I : Ideal R) (hI : IsAdic I) (phi : R →+* R)
    (hmap : ∀ x : R, x ∈ I → phi x ∈ I) : Continuous phi := by
  apply continuous_of_continuousAt_zero phi
  change Filter.Tendsto phi (nhds 0) (nhds (phi 0))
  rw [map_zero]
  apply hI.hasBasis_nhds_zero.tendsto_right_iff.mpr
  intro n _
  apply hI.hasBasis_nhds_zero.mem_iff.mpr
  refine ⟨n, trivial, ?_⟩
  intro x hx
  have hmapIdeal : I.map phi ≤ I :=
    Ideal.map_le_iff_le_comap.mpr hmap
  have hmapPow : (I ^ n).map phi ≤ I ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmapIdeal n
  exact hmapPow (Ideal.mem_map_of_mem phi hx)

/-- The semilinear Frobenius lift preserves the root ideal. -/
theorem padic_witt_frobenius
    (n : ℕ) (u : ℤ_[p]ˣ) (x : B p k n)
    (hx : x ∈ Ideal.span {cyclotomicWittRoot p k n}) :
    wittFrobeniusLift p k n u x ∈
      Ideal.span {cyclotomicWittRoot p k n} := by
  rw [Ideal.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  rw [map_mul, padic_frobenius_root]
  exact (Ideal.span {cyclotomicWittRoot p k n}).mul_mem_right _
    (padic_cyclotomic_witt p k n u⁻¹)

/-- The semilinear Frobenius lift is continuous on the complete root
algebra. -/
theorem continuous_witt_lift
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Continuous (wittFrobeniusLift p k n u) :=
  continuous_adic_ideal
    (Ideal.span {cyclotomicWittRoot p k n})
    (padic_cyclotomic_adic p k n)
    (wittFrobeniusLift p k n u)
    (padic_witt_frobenius p k n u)

set_option maxHeartbeats 2000000 in
-- Evaluation on relative points needs additional elaboration for the adic action.
/-- On every relative cyclotomic Lubin--Tate point, multiplication by a
`p`-adic scalar is evaluation of the corresponding binomial power series. -/
theorem padic_witt_smul
    (n : ℕ) (a : ℤ_[p])
    (x :
      let D := cyclotomicLubinDatum p
      let hI := padic_cyclotomic_adic p k n
      RelativeLubinPoints hI (padicWittRing p k n)
        D.pi D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit
        (padic_int_field p) (D.f : PowerSeries ℤ_[p])
        D.lubin_tate_card) :
    let D := cyclotomicLubinDatum p
    let hI := padic_cyclotomic_adic p k n
    (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit (padic_int_field p)
          (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map
            (padicWittRing p k n))
        (a • x) : B p k n) =
      PowerSeries.eval₂ (RingHom.id (B p k n))
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit (padic_int_field p)
            (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map
              (padicWittRing p k n)) x : B p k n)
        (PowerSeries.map (padicWittRing p k n)
          (padicBinomialEndomorphism p a)) := by
  dsimp only
  let D := cyclotomicLubinDatum p
  let hI := padic_cyclotomic_adic p k n
  let rho := padicWittRing p k n
  rw [relative_lubin_points]
  change MvPowerSeries.eval₂ (RingHom.id (B p k n)) _
      (MvPowerSeries.map rho
        (tateScalarIntertwiner D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit (padic_int_field p)
          (D.f : PowerSeries ℤ_[p]) (D.f : PowerSeries ℤ_[p])
          D.lubin_tate_card
          D.lubin_tate_card a)) = _
  have hscalar :
      tateScalarIntertwiner D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit (padic_int_field p)
          (D.f : PowerSeries ℤ_[p]) (D.f : PowerSeries ℤ_[p])
          D.lubin_tate_card
          D.lubin_tate_card a =
        powerSeriesUnary
          (padicBinomialEndomorphism p a) := by
    have hfSeries : (D.f : PowerSeries ℤ_[p]) =
        cyclotomicPowerSeries (R := ℤ_[p]) p := by
      simp [D, cyclotomicLubinDatum,
        padicCyclotomicLubin, cyclotomicPowerSeries]
    have hbin : LIntert
        (D.f : PowerSeries ℤ_[p]) (D.f : PowerSeries ℤ_[p])
        (fun _ : Fin 1 ↦ a)
        (powerSeriesUnary
          (padicBinomialEndomorphism p a)) := by
      apply unary_intertwiner_commutes
      · simpa only [← PowerSeries.coeff_zero_eq_constantCoeff_apply] using
          D.lubinTateSeries.1
      · exact endomorphism_constant_coeff p a
      · exact padic_binomial_endomorphism p a
      · calc
          PowerSeries.subst (padicBinomialEndomorphism p a)
              (D.f : PowerSeries ℤ_[p]) =
              PowerSeries.subst (padicBinomialEndomorphism p a)
                (cyclotomicPowerSeries (R := ℤ_[p]) p) := by rw [hfSeries]
          _ = PowerSeries.subst (cyclotomicPowerSeries (R := ℤ_[p]) p)
                (padicBinomialEndomorphism p a) :=
            endomorphism_subst_commute p a
          _ = PowerSeries.subst (D.f : PowerSeries ℤ_[p])
                (padicBinomialEndomorphism p a) := by
            rw [hfSeries]
    exact (tate_intertwiner D.pi D.pi_irreducible.ne_zero
      D.pi_irreducible.not_isUnit (padic_int_field p)
      (D.f : PowerSeries ℤ_[p]) (D.f : PowerSeries ℤ_[p])
      D.lubin_tate_card D.lubin_tate_card
      (fun _ : Fin 1 ↦ a) hbin).symm
  rw [hscalar]
  have hmap : MvPowerSeries.map rho
      (powerSeriesUnary (padicBinomialEndomorphism p a)) =
        powerSeriesUnary
          (PowerSeries.map rho
            (padicBinomialEndomorphism p a)) := by
    rw [powerSeriesUnary, powerSeriesUnary, PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero (by
        simp [FGLaw.unaryX]))]
    simp only [FGLaw.unaryX, MvPowerSeries.map_X]
  rw [hmap, powerSeriesUnary]
  change MvPowerSeries.eval₂ (RingHom.id (B p k n))
      (fun _ : Fin 1 ↦
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit (padic_int_field p)
            (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map rho)
          x : B p k n))
      (PowerSeries.subst FGLaw.unaryX
        (PowerSeries.map rho
          (padicBinomialEndomorphism p a))) = _
  have heval := mv_series_eval₂_subst_of_forall_constantCoeff_zero_adic
    hI (fun _ : Unit ↦ FGLaw.unaryX)
    (fun _ ↦ by simp [FGLaw.unaryX])
    (fun _ : Fin 1 ↦
      (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit (padic_int_field p)
          (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map rho)
        x : B p k n))
    (fun _ ↦ (FGLaw.APts.toIdeal hI
      ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
        D.pi_irreducible.not_isUnit (padic_int_field p)
        (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map rho)
      x).2)
    (PowerSeries.map rho
      (padicBinomialEndomorphism p a))
  simpa [PowerSeries.subst, FGLaw.unaryX] using heval

/-- Unit actions compose multiplicatively on the distinguished Witt root,
in the explicit power-series coordinate. -/
theorem padic_cyclotomic_value
    (n : ℕ) (u v : ℤ_[p]ˣ) :
    PowerSeries.eval₂ (RingHom.id (B p k n))
        (padicWittValue p k n v)
        (PowerSeries.map (padicWittRing p k n)
          (padicBinomialEndomorphism p (u : ℤ_[p]))) =
      padicWittValue p k n (u * v) := by
  unfold padicWittValue
  rw [← padic_witt_smul p k n (u : ℤ_[p])
    (padicWittPoint p k n v)]
  dsimp only
  have hpoint : (u : ℤ_[p]) •
      padicWittPoint p k n v =
      padicWittPoint p k n (u * v) := by
    unfold padicWittPoint
    change (u : ℤ_[p]) • ((v : ℤ_[p]) •
      padicCyclotomicPoint p k n) =
        ((u * v : ℤ_[p]ˣ) : ℤ_[p]) •
          padicCyclotomicPoint p k n
    calc
      (u : ℤ_[p]) • ((v : ℤ_[p]) •
          padicCyclotomicPoint p k n) =
          ((u : ℤ_[p]) * (v : ℤ_[p])) •
            padicCyclotomicPoint p k n :=
        smul_smul (u : ℤ_[p]) (v : ℤ_[p]) _
      _ = ((u * v : ℤ_[p]ˣ) : ℤ_[p]) •
          padicCyclotomicPoint p k n := by rfl
  rw [hpoint]

set_option maxHeartbeats 2000000 in
-- The exact-torsion quotient and convergent scalar evaluation unfold together.
/-- A `p`-adic unit translate of the Witt root is the usual cyclotomic
power indexed by its least residue modulo `p^(n+1)`. -/
theorem padic_witt_reduction
    (n : ℕ) (u : ℤ_[p]ˣ) :
    padicWittValue p k n u =
      (1 + cyclotomicWittRoot p k n) ^
          ((padicUnitReduction p (n + 1) u : ZMod (p ^ (n + 1))).val) - 1 := by
  let D := cyclotomicLubinDatum p
  let hI := padic_cyclotomic_adic p k n
  let y := padicCyclotomicPoint p k n
  let hy := witt_point_torsion p k n
  let I : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p]) ^ (n + 1)}
  let q : (ℤ_[p] ⧸ I)ˣ := Units.map (Ideal.Quotient.mk I).toMonoidHom u
  let m : ℕ :=
    (padicUnitReduction p (n + 1) u : ZMod (p ^ (n + 1))).val
  have hmk : Ideal.Quotient.mk I (m : ℤ_[p]) = (q : ℤ_[p] ⧸ I) := by
    apply (intZMod p (n + 1)).injective
    change intZMod p (n + 1)
        (Ideal.Quotient.mk I (m : ℤ_[p])) =
      intZMod p (n + 1)
        (Ideal.Quotient.mk I (u : ℤ_[p]))
    dsimp only [I]
    rw [z_mod_mk,
      z_mod_mk]
    rw [map_natCast]
    change ((m : ℕ) : ZMod (p ^ (n + 1))) =
      PadicInt.toZModPow (n + 1) (u : ℤ_[p])
    exact ZMod.natCast_zmod_val _
  have hyI : Ideal.torsionOf ℤ_[p] _ y = I := by
    simpa [D, I] using hy
  have hqu : orbitEmbeddingTorsion y hyI q =
      (u : ℤ_[p]) • y := by
    apply torsion_smul_mk
    rfl
  have hqm : orbitEmbeddingTorsion y hyI q =
      (m : ℤ_[p]) • y := by
    apply torsion_smul_mk
    exact hmk
  have hsmul : (u : ℤ_[p]) • y = (m : ℤ_[p]) • y := hqu.symm.trans hqm
  unfold padicWittValue
  change (FGLaw.APts.toIdeal hI _ ((u : ℤ_[p]) • y) :
      B p k n) = _
  rw [hsmul]
  rw [padic_witt_smul]
  rw [binomial_endomorphism_nat]
  have hmap : PowerSeries.map (padicWittRing p k n)
      (cyclotomicPowerSeries (R := ℤ_[p]) m) =
        cyclotomicPowerSeries (R := B p k n) m := by
    simp [cyclotomicPowerSeries]
  rw [hmap]
  have hcoe : cyclotomicPowerSeries (R := B p k n) m =
      (((1 + Polynomial.X : Polynomial (B p k n)) ^ m - 1 :
        Polynomial (B p k n)) : PowerSeries (B p k n)) := by
    symm
    simp [cyclotomicPowerSeries]
  rw [hcoe, PowerSeries.eval₂_coe]
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_X]
  rw [show (FGLaw.APts.toIdeal hI _ y : B p k n) =
      cyclotomicWittRoot p k n by
    exact padic_witt_point p k n]

/-- The semilinear Frobenius lift carries a unit translate of the
distinguished root to the translate obtained by multiplying by `u⁻¹`.
This is the root-coordinate form of its semilinear action. -/
theorem witt_frobenius_value
    (n : ℕ) (u v : ℤ_[p]ˣ) :
    wittFrobeniusLift p k n u
        (padicWittValue p k n v) =
      padicWittValue p k n (v * u⁻¹) := by
  let I := Ideal.span {cyclotomicWittRoot p k n}
  let hI := padic_cyclotomic_adic p k n
  let rho := padicWittRing p k n
  let phi := wittFrobeniusLift p k n u
  let root := cyclotomicWittRoot p k n
  let F := padicBinomialEndomorphism p (v : ℤ_[p])
  let U := PowerSeries.map rho F
  have hvalue : padicWittValue p k n v =
      PowerSeries.eval₂ (RingHom.id (B p k n))
        root U := by
    simpa [U] using
      (padic_cyclotomic_value p k n v 1).symm
  have hrootI : root ∈ I := Ideal.mem_span_singleton_self _
  have hphiI : ∀ x : B p k n, x ∈ I → phi x ∈ I :=
    padic_witt_frobenius p k n u
  have hcomp : phi.comp rho = rho := by
    ext a
    change phi (algebraMap (W p k) (B p k n)
      (padicIntWitt p k a)) =
        algebraMap (W p k) (B p k n) (padicIntWitt p k a)
    rw [padic_witt_coeff,
      frobenius_int_witt]
  have hnat :
      phi (PowerSeries.eval₂ (RingHom.id (B p k n)) root U) =
        PowerSeries.eval₂ (RingHom.id (B p k n)) (phi root)
          (PowerSeries.map (phi.comp rho) F) := by
    simpa only [PowerSeries.eval₂, U] using
      (eval₂_map_ringHom_of_forall_mem_adic hI hI rho phi
        (continuous_witt_lift p k n u)
        hphiI (fun _ : Unit ↦ root) (fun _ ↦ hrootI) F)
  rw [hcomp] at hnat
  rw [hvalue, hnat, padic_frobenius_root]
  exact padic_cyclotomic_value p k n v u⁻¹

/-- Inverse Witt Frobenius also fixes the scalar-extended cyclotomic
reduced polynomial. -/
theorem witt_reduced_symm
    (n : ℕ) :
    (padicWittReduced p k n).map
        (WittVector.frobeniusEquiv p k).symm.toRingHom =
      padicWittReduced p k n := by
  apply Polynomial.ext
  intro i
  simp only [Polynomial.coeff_map]
  apply (WittVector.frobeniusEquiv p k).injective
  change (WittVector.frobeniusEquiv p k)
      ((WittVector.frobeniusEquiv p k).symm
        ((padicWittReduced p k n).coeff i)) =
    (WittVector.frobeniusEquiv p k)
      ((padicWittReduced p k n).coeff i)
  rw [RingEquiv.apply_symm_apply]
  have h := congrArg (fun g : (W p k)[X] ↦ g.coeff i)
    (witt_reduced_frobenius p k n)
  exact (by simpa only [Polynomial.coeff_map,
    WittVector.frobeniusEquiv_apply] using h.symm)

/-- A unit translate is a root after applying inverse Witt Frobenius to
the coefficients. -/
theorem padic_witt_eval₂_frobeniusEquiv_symm_eq_zero
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let f := padicWittReduced p k n
    Polynomial.eval₂
        ((AdjoinRoot.of f).comp
          (WittVector.frobeniusEquiv p k).symm.toRingHom)
      (padicWittValue p k n u) f = 0 := by
  dsimp only
  let f := padicWittReduced p k n
  let y := padicWittValue p k n u
  rw [← Polynomial.eval_map]
  rw [← Polynomial.map_map]
  rw [witt_reduced_symm p k n]
  rw [Polynomial.eval_map]
  change Polynomial.eval₂ (AdjoinRoot.of f) y
    ((reducedLubinIterate
      (cyclotomicLubinDatum p).f n).map
        (padicIntWitt p k)) = 0
  rw [Polynomial.eval₂_map]
  change Polynomial.eval₂ (padicWittRing p k n) y
    (reducedLubinIterate
      (cyclotomicLubinDatum p).f n) = 0
  exact padic_point_reduced p k n u

/-- The explicit inverse of the semilinear Frobenius lift: inverse Witt
Frobenius on coefficients and the direct unit action on the root. -/
def padicWittInv (n : ℕ) (u : ℤ_[p]ˣ) :
    B p k n →+* B p k n :=
  let f := padicWittReduced p k n
  let y := padicWittValue p k n u
  AdjoinRoot.lift
    ((AdjoinRoot.of f).comp
      (WittVector.frobeniusEquiv p k).symm.toRingHom)
    y
    (padic_witt_eval₂_frobeniusEquiv_symm_eq_zero
      p k n u)

@[simp]
theorem padic_inv_coeff
    (n : ℕ) (u : ℤ_[p]ˣ) (a : W p k) :
    padicWittInv p k n u
        (algebraMap (W p k) (B p k n) a) =
      algebraMap (W p k) (B p k n)
        ((WittVector.frobeniusEquiv p k).symm a) := by
  exact AdjoinRoot.lift_of
    (f := padicWittReduced p k n)
    (h :=
      padic_witt_eval₂_frobeniusEquiv_symm_eq_zero
        p k n u)

@[simp]
theorem padic_inv_root
    (n : ℕ) (u : ℤ_[p]ˣ) :
    padicWittInv p k n u
        (cyclotomicWittRoot p k n) =
      padicWittValue p k n u := by
  exact AdjoinRoot.lift_root
    (f := padicWittReduced p k n)
    (h :=
      padic_witt_eval₂_frobeniusEquiv_symm_eq_zero
        p k n u)

/-- The inverse semilinear lift preserves the root ideal. -/
theorem padic_witt_inv
    (n : ℕ) (u : ℤ_[p]ˣ) (x : B p k n)
    (hx : x ∈ Ideal.span {cyclotomicWittRoot p k n}) :
    padicWittInv p k n u x ∈
      Ideal.span {cyclotomicWittRoot p k n} := by
  rw [Ideal.mem_span_singleton] at hx
  obtain ⟨a, rfl⟩ := hx
  rw [map_mul, padic_inv_root]
  exact (Ideal.span {cyclotomicWittRoot p k n}).mul_mem_right _
    (padic_cyclotomic_witt p k n u)

/-- The inverse semilinear Frobenius lift is continuous. -/
theorem continuous_witt_inv
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Continuous (padicWittInv p k n u) :=
  continuous_adic_ideal
    (Ideal.span {cyclotomicWittRoot p k n})
    (padic_cyclotomic_adic p k n)
    (padicWittInv p k n u)
    (padic_witt_inv p k n u)

/-- The inverse semilinear lift carries a unit translate by `v` to the
translate by `v * u`. -/
theorem padic_witt_value
    (n : ℕ) (u v : ℤ_[p]ˣ) :
    padicWittInv p k n u
        (padicWittValue p k n v) =
      padicWittValue p k n (v * u) := by
  let I := Ideal.span {cyclotomicWittRoot p k n}
  let hI := padic_cyclotomic_adic p k n
  let rho := padicWittRing p k n
  let phi := padicWittInv p k n u
  let root := cyclotomicWittRoot p k n
  let F := padicBinomialEndomorphism p (v : ℤ_[p])
  let U := PowerSeries.map rho F
  have hvalue : padicWittValue p k n v =
      PowerSeries.eval₂ (RingHom.id (B p k n))
        root U := by
    simpa [U] using
      (padic_cyclotomic_value p k n v 1).symm
  have hrootI : root ∈ I := Ideal.mem_span_singleton_self _
  have hphiI : ∀ x : B p k n, x ∈ I → phi x ∈ I :=
    padic_witt_inv p k n u
  have hcomp : phi.comp rho = rho := by
    ext a
    change phi (algebraMap (W p k) (B p k n)
      (padicIntWitt p k a)) =
        algebraMap (W p k) (B p k n) (padicIntWitt p k a)
    rw [padic_inv_coeff]
    apply congrArg (algebraMap (W p k) (B p k n))
    apply (WittVector.frobeniusEquiv p k).injective
    rw [RingEquiv.apply_symm_apply]
    exact (frobenius_int_witt p k a).symm
  have hnat :
      phi (PowerSeries.eval₂ (RingHom.id (B p k n)) root U) =
        PowerSeries.eval₂ (RingHom.id (B p k n)) (phi root)
          (PowerSeries.map (phi.comp rho) F) := by
    simpa only [PowerSeries.eval₂, U] using
      (eval₂_map_ringHom_of_forall_mem_adic hI hI rho phi
        (continuous_witt_inv p k n u)
        hphiI (fun _ : Unit ↦ root) (fun _ ↦ hrootI) F)
  rw [hcomp] at hnat
  rw [hvalue, hnat, padic_inv_root]
  exact padic_cyclotomic_value p k n v u

/-- The semilinear Frobenius lift is a ring automorphism of the complete
finite Witt-root algebra. -/
def padicWittFrobenius (n : ℕ) (u : ℤ_[p]ˣ) :
    B p k n ≃+* B p k n where
  toFun := wittFrobeniusLift p k n u
  invFun := padicWittInv p k n u
  left_inv x := by
    have hcomp :
        (padicWittInv p k n u).comp
            (wittFrobeniusLift p k n u) =
          RingHom.id (B p k n) := by
      apply AdjoinRoot.ringHom_ext
      · apply RingHom.ext
        intro a
        change padicWittInv p k n u
            (wittFrobeniusLift p k n u
              (algebraMap (W p k) (B p k n) a)) =
            algebraMap (W p k) (B p k n) a
        rw [padic_witt_coeff,
          padic_inv_coeff,
          ← WittVector.frobeniusEquiv_apply,
          RingEquiv.symm_apply_apply]
      · change padicWittInv p k n u
            (wittFrobeniusLift p k n u
              (cyclotomicWittRoot p k n)) = _
        rw [padic_frobenius_root,
          padic_witt_value]
        simp
        rfl
    exact DFunLike.congr_fun hcomp x
  right_inv x := by
    have hcomp :
        (wittFrobeniusLift p k n u).comp
            (padicWittInv p k n u) =
          RingHom.id (B p k n) := by
      apply AdjoinRoot.ringHom_ext
      · apply RingHom.ext
        intro a
        change wittFrobeniusLift p k n u
            (padicWittInv p k n u
              (algebraMap (W p k) (B p k n) a)) =
            algebraMap (W p k) (B p k n) a
        rw [padic_inv_coeff,
          padic_witt_coeff,
          ← WittVector.frobeniusEquiv_apply,
          RingEquiv.apply_symm_apply]
      · change wittFrobeniusLift p k n u
            (padicWittInv p k n u
              (cyclotomicWittRoot p k n)) = _
        rw [padic_inv_root,
          witt_frobenius_value]
        simp
        rfl
    exact DFunLike.congr_fun hcomp x
  map_add' x y := map_add _ x y
  map_mul' x y := map_mul _ x y

/-- The semilinear Frobenius automorphism on the common fraction field
containing the finite cyclotomic root field. -/
def padicFractionFrobenius
    (n : ℕ) (u : ℤ_[p]ˣ) : C p k n ≃+* C p k n :=
  IsFractionRing.ringEquivOfRingEquiv
    (padicWittFrobenius p k n u)

@[simp]
theorem witt_fraction_algebra
    (n : ℕ) (u : ℤ_[p]ˣ) (x : B p k n) :
    padicFractionFrobenius p k n u
        (algebraMap (B p k n) (C p k n) x) =
      algebraMap (B p k n) (C p k n)
        (wittFrobeniusLift p k n u x) := by
  exact IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (padicWittFrobenius p k n u) x

/-- The fraction-field semilinear Frobenius fixes the embedded copy of
`Q_p`. -/
@[simp]
theorem cyclotomic_witt_fraction
    (n : ℕ) (u : ℤ_[p]ˣ) (x : ℚ_[p]) :
    padicFractionFrobenius p k n u
        (wittRootFraction p k n x) =
      wittRootFraction p k n x := by
  have hhom :
      (padicFractionFrobenius p k n u).toRingHom.comp
          (wittRootFraction p k n) =
        wittRootFraction p k n := by
    apply IsFractionRing.ringHom_ext (A := ℤ_[p])
    intro a
    simp only [RingHom.comp_apply,
      root_fraction_algebra]
    change padicFractionFrobenius p k n u
        (algebraMap (B p k n) (C p k n)
          (padicWittRing p k n a)) =
      algebraMap (B p k n) (C p k n)
        (padicWittRing p k n a)
    rw [witt_fraction_algebra]
    change algebraMap (B p k n) (C p k n)
        (wittFrobeniusLift p k n u
          (algebraMap (W p k) (B p k n) (padicIntWitt p k a))) =
      algebraMap (B p k n) (C p k n)
        (algebraMap (W p k) (B p k n) (padicIntWitt p k a))
    rw [padic_witt_coeff,
      frobenius_int_witt]
  exact DFunLike.congr_fun hhom x

/-- The common Witt fraction field, regarded as a `Q_p`-algebra through
the explicit coefficient embedding. -/
noncomputable instance wittFractionAlgebra (n : ℕ) :
    Algebra ℚ_[p] (C p k n) :=
  (wittRootFraction p k n).toAlgebra

@[simp]
theorem padic_witt_algebra
    (n : ℕ) (x : ℚ_[p]) :
    algebraMap ℚ_[p] (C p k n) x =
      wittRootFraction p k n x :=
  rfl

/-- The semilinear Frobenius is a `Q_p`-algebra automorphism of the common
fraction field. -/
def wittFractionFrobenius
    (n : ℕ) (u : ℤ_[p]ˣ) : C p k n ≃ₐ[ℚ_[p]] C p k n where
  __ := padicFractionFrobenius p k n u
  commutes' x :=
    cyclotomic_witt_fraction p k n u x

/-- The distinguished cyclotomic root-field embedding into the common
Witt fraction field, as a `Q_p`-algebra homomorphism. -/
def padicWittFraction (n : ℕ) :
    (cyclotomicLubinDatum p).RootField ℚ_[p] n →ₐ[ℚ_[p]]
      C p k n where
  toRingHom := padicCyclotomicFraction p k n
  commutes' x := by
    change padicCyclotomicFraction p k n
        (algebraMap ℚ_[p]
          ((cyclotomicLubinDatum p).RootField ℚ_[p] n) x) =
      wittRootFraction p k n x
    exact AdjoinRoot.lift_of
      (f := (cyclotomicLubinDatum p).reducedPolynomial ℚ_[p] n)
      (h := cyclotomic_witt_root₂_reduced_eq_zero p k n)

@[simp]
theorem padic_witt_fraction (n : ℕ) :
    padicWittFraction p k n
        ((cyclotomicLubinDatum p).root ℚ_[p] n) =
      algebraMap (B p k n) (C p k n)
        (cyclotomicWittRoot p k n) :=
  padic_cyclotomic_fraction p k n

/-- On the distinguished root, the fraction-field Frobenius is precisely
the inverse-unit Lubin--Tate action. -/
theorem witt_fraction_root
    (n : ℕ) (u : ℤ_[p]ˣ) :
    wittFractionFrobenius p k n u
        (padicWittFraction p k n
          ((cyclotomicLubinDatum p).root ℚ_[p] n)) =
      algebraMap (B p k n) (C p k n)
        (padicWittValue p k n u⁻¹) := by
  rw [padic_witt_fraction]
  change padicFractionFrobenius p k n u
      (algebraMap (B p k n) (C p k n)
        (cyclotomicWittRoot p k n)) = _
  rw [
    witt_fraction_algebra,
    padic_frobenius_root]

/-- The explicit quotient-unit orbit transported from the
valuation-integer root field to the `Z_p` root-field presentation used by
the Witt construction. -/
noncomputable def padicCyclotomicOrbit (n : ℕ) :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ ≃*
      ((cyclotomicLubinDatum p).RootField ℚ_[p] n ≃ₐ[ℚ_[p]]
        (cyclotomicLubinDatum p).RootField ℚ_[p] n) :=
  (padicIntegerCyclotomic p n).trans
    (padicIntegerAlg p n).autCongr

@[simp]
theorem padic_cyclotomic_orbit
    (n : ℕ)
    (q : let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
      let D := padicLubinDatum p
      (A ⧸ Ideal.span {D.pi ^ (n + 1)})ˣ) :
    padicCyclotomicOrbit p n q
        ((cyclotomicLubinDatum p).root ℚ_[p] n) =
      (1 + (cyclotomicLubinDatum p).root ℚ_[p] n) ^
          ((padicZMod p (n + 1) q :
            ZMod (p ^ (n + 1))).val) - 1 := by
  let e := padicIntegerAlg p n
  change e
      (padicIntegerCyclotomic p n q
        (e.symm ((cyclotomicLubinDatum p).root ℚ_[p] n))) = _
  rw [show e.symm ((cyclotomicLubinDatum p).root ℚ_[p] n) =
      (padicLubinDatum p).root ℚ_[p] n by
    apply e.injective
    rw [e.apply_symm_apply]
    exact (padic_integer_alg p n).symm]
  rw [padic_integer_cyclotomic]
  simp only [map_sub, map_pow, map_add, map_one]
  rw [show e ((padicLubinDatum p).root ℚ_[p] n) =
      (cyclotomicLubinDatum p).root ℚ_[p] n by
    exact padic_integer_alg p n]

/-- The Witt Frobenius/unit automorphism restricts on the finite
cyclotomic root field to the inverse-unit Lubin--Tate Galois action. -/
theorem padic_fraction_restrict
    (n : ℕ) (u : ℤ_[p]ˣ) :
    (wittFractionFrobenius p k n u).toAlgHom.comp
        (padicWittFraction p k n) =
      (padicWittFraction p k n).comp
        (padicCyclotomicOrbit p n
          (padicIntInteger p (n + 1) u⁻¹)).toAlgHom := by
  apply AdjoinRoot.algHom_ext
  change wittFractionFrobenius p k n u
      (padicWittFraction p k n
        ((cyclotomicLubinDatum p).root ℚ_[p] n)) =
    padicWittFraction p k n
      (padicCyclotomicOrbit p n
        (padicIntInteger p (n + 1) u⁻¹)
          ((cyclotomicLubinDatum p).root ℚ_[p] n))
  rw [witt_fraction_root]
  rw [padic_cyclotomic_orbit]
  simp only [map_sub, map_pow, map_add, map_one,
    padic_witt_fraction]
  rw [padic_witt_reduction]
  rw [padic_z_reduction]
  simp [padicUnitReduction]

end

end Submission.CField.LTate

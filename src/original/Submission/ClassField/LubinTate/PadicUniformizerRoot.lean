import Submission.ClassField.LubinTate.PadicRootAction
import Submission.ClassField.LubinTate.PadicRootDVR
import Submission.ClassField.LubinTate.Independence
import Submission.ClassField.LubinTate.FiniteSubextension

/-!
# The fixed basic Lubin--Tate root after changing uniformizer

The semilinear Witt-vector series from Proposition I.3.10 is evaluated in
the complete finite cyclotomic root algebra.  Witt Frobenius on coefficients
and the inverse-unit action on the cyclotomic root cancel exactly, so the
resulting basic Lubin--Tate torsion point is fixed by the semilinear lift.
-/

namespace Submission.CField.LTate

open PowerSeries
open Submission.CField.FGroups
open scoped IsMulCommutative NormedField Topology

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]

local instance padicWittUniformizerRootValuativeRel : ValuativeRel ℚ_[p] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[p]))

local instance padicWittUniformizerRootCompatible :
    Valuation.Compatible (NormedField.valuation (K := ℚ_[p])) :=
  Valuation.Compatible.ofValuation (NormedField.valuation (K := ℚ_[p]))

local instance padicWittUniformizerRootLocalField :
    IsNonarchimedeanLocalField ℚ_[p] := by
  haveI htop : IsValuativeTopology ℚ_[p] := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ 𝓝 (0 : ℚ_[p]) ↔
        ∃ γ : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := ℚ_[p])))ˣ,
          {x | (NormedField.valuation (K := ℚ_[p])).restrict x < γ.1} ⊆ s from
      (NormedField.toValued (K := ℚ_[p])).is_topological_valuation s]
    simpa using
      (NormedField.valuation (K := ℚ_[p]))
        |>.exists_setOf_restrict_le_iff 0 s
  haveI hnontrivial : ValuativeRel.IsNontrivial ℚ_[p] :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := ℚ_[p]))).mpr inferInstance
  exact
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := hnontrivial }

local instance padicCyclotomicUniformizerRootResidueFintype :
    Fintype (ℤ_[p] ⧸ Ideal.span {(cyclotomicLubinDatum p).pi}) := by
  change Fintype (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})
  infer_instance

private abbrev W := WittVector p k
private abbrev B (n : ℕ) := PadicWittRing p k n
private abbrev C (n : ℕ) := FractionRing (B p k n)

/-- The explicit `ℤ_[p]` cyclotomic root-field model is Galois. -/
noncomputable instance padicFieldGalois (n : ℕ) :
    IsGalois ℚ_[p]
      ((cyclotomicLubinDatum p).RootField ℚ_[p] n) :=
  IsGalois.of_algEquiv
    (padicIntegerAlg p n)

/-- Its Galois group is abelian. -/
noncomputable instance padicCyclotomicCommutative (n : ℕ) :
    IsMulCommutative
      Gal((cyclotomicLubinDatum p).RootField ℚ_[p] n/ℚ_[p]) := by
  let e := padicIntegerAlg p n
  refine ⟨⟨fun σ τ ↦ (e.autCongr.symm).injective ?_⟩⟩
  simpa only [map_mul] using
    mul_comm (e.autCongr.symm σ) (e.autCongr.symm τ)

/-- The valuation-integer model of the basic `p * u` root field is Galois
by the generic finite Lubin--Tate theorem. -/
noncomputable instance padicRootGalois
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsGalois ℚ_[p]
      ((lubinTateDatum p u).RootField ℚ_[p] n) := by
  exact (lubinTateDatum p u).root_field_galois ℚ_[p]
    (padic_integer_field p u) n

/-- The same Galois structure on the explicit `ℤ_[p]` model used by the
Witt-root construction. -/
noncomputable instance padicBasicGalois
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsGalois ℚ_[p]
      ((padicTateDatum p u).RootField ℚ_[p] n) :=
  IsGalois.of_algEquiv
    (padicIntegerBasic p u n)

/-- The valuation-integer basic Lubin--Tate Galois group is abelian. -/
noncomputable instance padicRootCommutative
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsMulCommutative
      Gal((lubinTateDatum p u).RootField ℚ_[p] n/ℚ_[p]) :=
  (lubinTateDatum p u).root_aut_commutative
    ℚ_[p] (padic_integer_field p u) n

/-- Hence the explicit basic root-field Galois group is abelian as well. -/
noncomputable instance padicBasicCommutative
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsMulCommutative
      Gal((padicTateDatum p u).RootField ℚ_[p] n/ℚ_[p]) := by
  let e := padicIntegerBasic p u n
  refine ⟨⟨fun σ τ ↦ (e.autCongr.symm).injective ?_⟩⟩
  simpa only [map_mul] using
    mul_comm (e.autCongr.symm σ) (e.autCongr.symm τ)

/-- Reassociating the definition of the semilinear conjugate gives the
intertwining equation used on torsion points. -/
theorem semilinear_intertwines_theta
    {R : Type*} [CommRing R] (sigma : R →+* R)
    {theta inverseTheta f g U : PowerSeries R}
    (htheta0 : constantCoeff theta = 0)
    (hinverse0 : constantCoeff inverseTheta = 0)
    (hf0 : constantCoeff f = 0)
    (hU0 : constantCoeff U = 0)
    (hthetaInverse : subst theta inverseTheta = X)
    (hsemilinear : PowerSeries.map sigma theta = subst U theta)
    (hconjugate : semilinearConjugate sigma theta inverseTheta f = g) :
    subst theta g = subst (subst f U) theta := by
  have hthetaSubst : PowerSeries.HasSubst theta :=
    PowerSeries.HasSubst.of_constantCoeff_zero' htheta0
  have hinverseSubst : PowerSeries.HasSubst inverseTheta :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hinverse0
  have hfSubst : PowerSeries.HasSubst f :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  have hUSubst : PowerSeries.HasSubst U :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hU0
  calc
    subst theta g = subst theta
        (semilinearConjugate sigma theta inverseTheta f) := by rw [hconjugate]
    _ = subst theta
        (subst inverseTheta (subst f (PowerSeries.map sigma theta))) := by
      rw [semilinear_conjugate_nested sigma hinverse0 hf0]
    _ = subst (subst theta inverseTheta)
        (subst f (PowerSeries.map sigma theta)) := by
      exact subst_comp_subst_apply hinverseSubst hthetaSubst
        (subst f (PowerSeries.map sigma theta))
    _ = subst X (subst f (PowerSeries.map sigma theta)) := by
      rw [hthetaInverse]
    _ = subst f (PowerSeries.map sigma theta) := by
      rw [← PowerSeries.map_algebraMap_eq_subst_X
        (R := R) (S := R) (subst f (PowerSeries.map sigma theta))]
      change PowerSeries.map (RingHom.id R)
        (subst f (PowerSeries.map sigma theta)) = _
      exact congrFun (PowerSeries.map_id (R := R))
        (subst f (PowerSeries.map sigma theta))
    _ = subst f (subst U theta) := by rw [hsemilinear]
    _ = subst (subst f U) theta := by
      exact subst_comp_subst_apply hUSubst hfSubst theta

/-- Iterating an evaluated intertwining equation preserves the same
conjugacy relation on the complete adic ideal. -/
theorem adic_iterate_intertwines
    {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [IsTopologicalRing R] [T2Space R] [CompleteSpace R]
    {I : Ideal R} (hI : IsAdic I)
    (f g theta : PowerSeries R)
    (hf0 : constantCoeff f = 0)
    (hg0 : constantCoeff g = 0)
    (htheta0 : constantCoeff theta = 0)
    (hintertwines : subst theta g = subst f theta)
    (m : ℕ) (x : I) :
    (seriesAdic hI g hg0)^[m]
        (seriesAdic hI theta htheta0 x) =
      seriesAdic hI theta htheta0
        ((seriesAdic hI f hf0)^[m] x) := by
  exact (Function.Semiconj.iterate_right
    (fun x ↦ (series_adic_intertwines hI f g theta
      hf0 hg0 htheta0 hintertwines x).symm) m x).symm

/-- Function iteration of convergent evaluation agrees with evaluation of
the formal substitution iterate. -/
theorem adic_iterate_substitution
    {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [IsTopologicalRing R] [T2Space R] [CompleteSpace R]
    {I : Ideal R} (hI : IsAdic I)
    (f : PowerSeries R) (hf0 : constantCoeff f = 0)
    (m : ℕ) (x : I) :
    (seriesAdic hI f hf0)^[m] x =
      seriesAdic hI (substitutionIterate f m)
        (substitution_iterate_coeff hf0 m) x := by
  induction m with
  | zero =>
      exact (series_adic_x hI x).symm
  | succ m ih =>
      calc
        (seriesAdic hI f hf0)^[m + 1] x =
            seriesAdic hI f hf0
              ((seriesAdic hI f hf0)^[m] x) := by
          rw [Function.iterate_succ_apply']
        _ = seriesAdic hI f hf0
              (seriesAdic hI (substitutionIterate f m)
                (substitution_iterate_coeff hf0 m) x) := by
          rw [ih]
        _ = seriesAdic hI
              (PowerSeries.subst (substitutionIterate f m) f)
              (PowerSeries.constantCoeff_subst_eq_zero
                (substitution_iterate_coeff hf0 m) f hf0) x :=
          (series_adic_subst hI f (substitutionIterate f m)
            hf0 (substitution_iterate_coeff hf0 m) x).symm
        _ = seriesAdic hI (substitutionIterate f (m + 1))
              (substitution_iterate_coeff hf0 (m + 1)) x := by
          rfl

/-- Evaluation of a Witt-coefficient series at the distinguished finite
cyclotomic root. -/
def wittThetaValue (n : ℕ)
    (theta : PowerSeries (W p k)) : B p k n :=
  PowerSeries.eval₂ (RingHom.id (B p k n))
    (cyclotomicWittRoot p k n)
    (PowerSeries.map (algebraMap (W p k) (B p k n)) theta)

/-- A zero-constant Witt series evaluates inside the root ideal. -/
theorem padic_witt_theta
    (n : ℕ) (theta : PowerSeries (W p k))
    (htheta0 : constantCoeff theta = 0) :
    wittThetaValue p k n theta ∈
      Ideal.span {cyclotomicWittRoot p k n} := by
  let I := Ideal.span {cyclotomicWittRoot p k n}
  let hI := padic_cyclotomic_adic p k n
  apply constant_coeff_adic hI
  · exact Ideal.mem_span_singleton_self _
  · rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, htheta0, map_zero]
    exact I.zero_mem

set_option maxHeartbeats 3000000 in
-- Evaluating the semilinear series in the finite Witt-root algebra is reduction-heavy.
/-- The evaluated semilinear identity from Proposition I.3.10.  The
Frobenius lift applies `F` to the coefficients and `[u⁻¹]` to the root;
the equation `F(theta) = theta ∘ [u]` therefore makes `theta(root)` fixed. -/
theorem witt_theta_value
    (n : ℕ) (u : ℤ_[p]ˣ)
    (theta : PowerSeries (W p k))
    (htheta0 : constantCoeff theta = 0)
    (hsemilinear :
      PowerSeries.map WittVector.frobenius theta =
        PowerSeries.subst
          (PowerSeries.map (padicIntWitt p k)
            (padicBinomialEndomorphism p (u : ℤ_[p]))) theta) :
    wittFrobeniusLift p k n u
        (wittThetaValue p k n theta) =
      wittThetaValue p k n theta := by
  let I := Ideal.span {cyclotomicWittRoot p k n}
  let hI := padic_cyclotomic_adic p k n
  let rho : W p k →+* B p k n := algebraMap (W p k) (B p k n)
  let phi := wittFrobeniusLift p k n u
  let root := cyclotomicWittRoot p k n
  let y := padicWittValue p k n u⁻¹
  let U := PowerSeries.map (padicIntWitt p k)
    (padicBinomialEndomorphism p (u : ℤ_[p]))
  let thetaB := PowerSeries.map rho theta
  let UB := PowerSeries.map rho U
  have hrootI : root ∈ I := Ideal.mem_span_singleton_self _
  have hyI : y ∈ I :=
    padic_cyclotomic_witt p k n u⁻¹
  have hphiI : ∀ x : B p k n, x ∈ I → phi x ∈ I :=
    padic_witt_frobenius p k n u
  have hcomp : phi.comp rho = rho.comp WittVector.frobenius := by
    ext a
    exact padic_witt_coeff p k n u a
  have hnat :
      phi (PowerSeries.eval₂ (RingHom.id (B p k n)) root thetaB) =
        PowerSeries.eval₂ (RingHom.id (B p k n)) (phi root)
          (PowerSeries.map (phi.comp rho) theta) := by
    simpa only [PowerSeries.eval₂] using
      (eval₂_map_ringHom_of_forall_mem_adic hI hI rho phi
        (continuous_witt_lift p k n u)
        hphiI (fun _ : Unit ↦ root) (fun _ ↦ hrootI) theta)
  have hmapComp :
      PowerSeries.map (phi.comp rho) theta =
        PowerSeries.map rho (PowerSeries.map WittVector.frobenius theta) := by
    rw [hcomp]
    apply PowerSeries.ext
    intro i
    rfl
  have hthetaB0 : constantCoeff thetaB = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, htheta0, map_zero]
  have hU0 : constantCoeff U = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply,
      endomorphism_constant_coeff, map_zero]
  have hUB0 : constantCoeff UB = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, hU0, map_zero]
  have hmapSubst :
      PowerSeries.map rho (PowerSeries.subst U theta) =
        PowerSeries.subst UB thetaB := by
    exact PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' hU0) theta
  let yI : I := ⟨y, hyI⟩
  have hsubst :
      PowerSeries.eval₂ (RingHom.id (B p k n)) y
          (PowerSeries.subst UB thetaB) =
        PowerSeries.eval₂ (RingHom.id (B p k n))
          (PowerSeries.eval₂ (RingHom.id (B p k n)) y UB) thetaB := by
    have h := congrArg Subtype.val
      (series_adic_subst hI thetaB UB hthetaB0 hUB0 yI)
    exact h
  have hcancel :
      PowerSeries.eval₂ (RingHom.id (B p k n)) y UB = root := by
    change PowerSeries.eval₂ (RingHom.id (B p k n))
        (padicWittValue p k n u⁻¹)
        (PowerSeries.map (padicWittRing p k n)
          (padicBinomialEndomorphism p (u : ℤ_[p]))) = root
    rw [padic_cyclotomic_value p k n u u⁻¹]
    have hu : u * u⁻¹ = 1 := mul_inv_cancel u
    rw [hu, padic_witt_one]
  change phi (PowerSeries.eval₂ (RingHom.id (B p k n)) root thetaB) =
    PowerSeries.eval₂ (RingHom.id (B p k n)) root thetaB
  calc
    phi (PowerSeries.eval₂ (RingHom.id (B p k n)) root thetaB) =
        PowerSeries.eval₂ (RingHom.id (B p k n)) (phi root)
          (PowerSeries.map (phi.comp rho) theta) := hnat
    _ = PowerSeries.eval₂ (RingHom.id (B p k n)) y
          (PowerSeries.map rho (PowerSeries.map WittVector.frobenius theta)) := by
      rw [padic_frobenius_root, hmapComp]
    _ = PowerSeries.eval₂ (RingHom.id (B p k n)) y
          (PowerSeries.map rho (PowerSeries.subst U theta)) := by
      rw [hsemilinear]
    _ = PowerSeries.eval₂ (RingHom.id (B p k n)) y
          (PowerSeries.subst UB thetaB) := by rw [hmapSubst]
    _ = PowerSeries.eval₂ (RingHom.id (B p k n))
          (PowerSeries.eval₂ (RingHom.id (B p k n)) y UB) thetaB := hsubst
    _ = PowerSeries.eval₂ (RingHom.id (B p k n)) root thetaB := by
      rw [hcancel]

set_option maxHeartbeats 2000000 in
-- The source conjugate and the relative-point scalar action unfold together.
/-- The source-side conjugate `U ∘ f` acts on relative cyclotomic points as
the scalar `p*u`. -/
theorem padic_witt_conjugate
    (n : ℕ) (u : ℤ_[p]ˣ)
    (z :
      let D := cyclotomicLubinDatum p
      let hI := padic_cyclotomic_adic p k n
      RelativeLubinPoints hI (padicWittRing p k n)
        D.pi D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit
        (padic_int_field p) (D.f : PowerSeries ℤ_[p])
        D.lubin_tate_card) :
    let D := cyclotomicLubinDatum p
    let hI := padic_cyclotomic_adic p k n
    let rhoW : W p k →+* B p k n := algebraMap (W p k) (B p k n)
    let fW := PowerSeries.map (padicIntWitt p k) (D.f : PowerSeries ℤ_[p])
    let U := PowerSeries.map (padicIntWitt p k)
      (padicBinomialEndomorphism p (u : ℤ_[p]))
    PowerSeries.eval₂ (RingHom.id (B p k n))
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit (padic_int_field p)
            (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map
              (padicWittRing p k n)) z : B p k n)
        (PowerSeries.map rhoW (PowerSeries.subst fW U)) =
      (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit (padic_int_field p)
          (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map
            (padicWittRing p k n))
        (((p : ℤ_[p]) * (u : ℤ_[p])) • z) : B p k n) := by
  dsimp only
  let D := cyclotomicLubinDatum p
  let hI := padic_cyclotomic_adic p k n
  let rhoZ := padicWittRing p k n
  let rhoW : W p k →+* B p k n := algebraMap (W p k) (B p k n)
  let fW := PowerSeries.map (padicIntWitt p k) (D.f : PowerSeries ℤ_[p])
  let U := PowerSeries.map (padicIntWitt p k)
    (padicBinomialEndomorphism p (u : ℤ_[p]))
  let x : B p k n := FGLaw.APts.toIdeal hI
    ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
      D.pi_irreducible.not_isUnit (padic_int_field p)
      (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map rhoZ) z
  have hf0 : constantCoeff fW = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    rw [show coeff 0 (D.f : PowerSeries ℤ_[p]) = 0 by
      simpa only [← coeff_zero_eq_constantCoeff_apply] using
        D.lubinTateSeries.1, map_zero]
  have hmapSubst : PowerSeries.map rhoW (PowerSeries.subst fW U) =
      PowerSeries.subst (PowerSeries.map rhoW fW)
        (PowerSeries.map rhoW U) :=
    PowerSeries.map_subst
      (PowerSeries.HasSubst.of_constantCoeff_zero' hf0) U
  rw [hmapSubst]
  have hfEval : PowerSeries.eval₂ (RingHom.id (B p k n)) x
      (PowerSeries.map rhoW fW) =
      (FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit (padic_int_field p)
          (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map rhoZ)
        ((p : ℤ_[p]) • z) : B p k n) := by
    have h := relative_points_uniformizer
      hI rhoZ D.pi D.pi_irreducible.ne_zero D.pi_irreducible.not_isUnit
      (padic_int_field p) (D.f : PowerSeries ℤ_[p])
      D.lubin_tate_card z
    change _ = PowerSeries.eval₂ (RingHom.id (B p k n)) x
      (PowerSeries.map rhoZ (D.f : PowerSeries ℤ_[p])) at h
    rw [show PowerSeries.map rhoW fW =
        PowerSeries.map rhoZ (D.f : PowerSeries ℤ_[p]) by
      apply PowerSeries.ext
      intro i
      rfl]
    exact h.symm
  have hU0 : constantCoeff (PowerSeries.map rhoW U) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_map, coeff_zero_eq_constantCoeff_apply,
      endomorphism_constant_coeff, map_zero, map_zero]
  have hsubst := series_adic_subst hI
    (PowerSeries.map rhoW U) (PowerSeries.map rhoW fW)
    hU0 (by
      rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        coeff_zero_eq_constantCoeff_apply, hf0, map_zero])
    ⟨x, (FGLaw.APts.toIdeal hI _ z).property⟩
  have hsubst' : PowerSeries.eval₂ (RingHom.id (B p k n)) x
        (PowerSeries.subst (PowerSeries.map rhoW fW)
          (PowerSeries.map rhoW U)) =
      PowerSeries.eval₂ (RingHom.id (B p k n))
        (PowerSeries.eval₂ (RingHom.id (B p k n)) x
          (PowerSeries.map rhoW fW))
        (PowerSeries.map rhoW U) := by
    simpa only [coe_series_adic] using congrArg Subtype.val hsubst
  change PowerSeries.eval₂ (RingHom.id (B p k n)) x
      (PowerSeries.subst (PowerSeries.map rhoW fW)
        (PowerSeries.map rhoW U)) = _
  rw [hsubst']
  rw [hfEval]
  rw [show PowerSeries.map rhoW U =
      PowerSeries.map rhoZ (padicBinomialEndomorphism p (u : ℤ_[p])) by
    apply PowerSeries.ext
    intro i
    rfl]
  rw [← padic_witt_smul p k n (u : ℤ_[p])
    ((p : ℤ_[p]) • z)]
  have hpoint : (u : ℤ_[p]) • ((p : ℤ_[p]) • z) =
      ((p : ℤ_[p]) * (u : ℤ_[p])) • z := by
    calc
      (u : ℤ_[p]) • ((p : ℤ_[p]) • z) =
          ((u : ℤ_[p]) * (p : ℤ_[p])) • z :=
        smul_smul (u : ℤ_[p]) (p : ℤ_[p]) z
      _ = ((p : ℤ_[p]) * (u : ℤ_[p])) • z := by
        rw [mul_comm]
  rw [hpoint]

set_option maxHeartbeats 2000000 in
-- Iterated substitution at the distinguished root requires a larger reduction budget.
/-- Every iterate of the source conjugate on the distinguished cyclotomic
root is the corresponding power of the scalar `p*u`. -/
theorem conjugate_iterate_root
    (n : ℕ) (u : ℤ_[p]ˣ) (m : ℕ) :
    let D := cyclotomicLubinDatum p
    let hI := padic_cyclotomic_adic p k n
    let rhoW : W p k →+* B p k n := algebraMap (W p k) (B p k n)
    let fW := PowerSeries.map (padicIntWitt p k)
      (D.f : PowerSeries ℤ_[p])
    let U := PowerSeries.map (padicIntWitt p k)
      (padicBinomialEndomorphism p (u : ℤ_[p]))
    let sourceB := PowerSeries.map rhoW (PowerSeries.subst fW U)
    let hsource0 : constantCoeff sourceB = 0 := by
      have hfW0 : constantCoeff fW = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
        rw [show coeff 0 (D.f : PowerSeries ℤ_[p]) = 0 by
          simpa only [← coeff_zero_eq_constantCoeff_apply] using
            D.lubinTateSeries.1, map_zero]
      have hU0 : constantCoeff U = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
          coeff_zero_eq_constantCoeff_apply,
          endomorphism_constant_coeff, map_zero]
      have hs0 : constantCoeff (PowerSeries.subst fW U) = 0 :=
        PowerSeries.constantCoeff_subst_eq_zero hfW0 U hU0
      rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        coeff_zero_eq_constantCoeff_apply, hs0, map_zero]
    (seriesAdic hI sourceB hsource0)^[m]
        (FGLaw.APts.toIdeal hI
          ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
            D.pi_irreducible.not_isUnit (padic_int_field p)
            (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map
              (padicWittRing p k n))
          (padicCyclotomicPoint p k n)) =
      FGLaw.APts.toIdeal hI
        ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
          D.pi_irreducible.not_isUnit (padic_int_field p)
          (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map
            (padicWittRing p k n))
        ((((p : ℤ_[p]) * (u : ℤ_[p])) ^ m) •
          padicCyclotomicPoint p k n) := by
  dsimp only
  let D := cyclotomicLubinDatum p
  let hI := padic_cyclotomic_adic p k n
  let rhoW : W p k →+* B p k n := algebraMap (W p k) (B p k n)
  let fW := PowerSeries.map (padicIntWitt p k)
    (D.f : PowerSeries ℤ_[p])
  let U := PowerSeries.map (padicIntWitt p k)
    (padicBinomialEndomorphism p (u : ℤ_[p]))
  let sourceB := PowerSeries.map rhoW (PowerSeries.subst fW U)
  have hsource0 : constantCoeff sourceB = 0 := by
    have hfW0 : constantCoeff fW = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
      rw [show coeff 0 (D.f : PowerSeries ℤ_[p]) = 0 by
        simpa only [← coeff_zero_eq_constantCoeff_apply] using
          D.lubinTateSeries.1, map_zero]
    have hU0 : constantCoeff U = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        coeff_zero_eq_constantCoeff_apply,
        endomorphism_constant_coeff, map_zero]
    have hs0 : constantCoeff (PowerSeries.subst fW U) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hfW0 U hU0
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, hs0, map_zero]
  induction m with
  | zero =>
      rw [Function.iterate_zero_apply, pow_zero]
      have hpoint : (1 : ℤ_[p]) • padicCyclotomicPoint p k n =
          padicCyclotomicPoint p k n :=
        one_smul ℤ_[p] (padicCyclotomicPoint p k n)
      rw [hpoint]
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      apply Subtype.ext
      change PowerSeries.eval₂ (RingHom.id (B p k n))
          (FGLaw.APts.toIdeal hI
            ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
              D.pi_irreducible.not_isUnit (padic_int_field p)
              (D.f : PowerSeries ℤ_[p])
              D.lubin_tate_card).map
                (padicWittRing p k n))
            ((((p : ℤ_[p]) * (u : ℤ_[p])) ^ m) •
              padicCyclotomicPoint p k n) : B p k n)
          sourceB = _
      rw [padic_witt_conjugate p k n u
        ((((p : ℤ_[p]) * (u : ℤ_[p])) ^ m) •
          padicCyclotomicPoint p k n)]
      congr 2
      calc
        ((p : ℤ_[p]) * (u : ℤ_[p])) •
            ((((p : ℤ_[p]) * (u : ℤ_[p])) ^ m) •
              padicCyclotomicPoint p k n) =
            (((p : ℤ_[p]) * (u : ℤ_[p])) *
              (((p : ℤ_[p]) * (u : ℤ_[p])) ^ m)) •
              padicCyclotomicPoint p k n :=
          smul_smul _ _ _
        _ = (((p : ℤ_[p]) * (u : ℤ_[p])) ^ (m + 1)) •
              padicCyclotomicPoint p k n := by
          rw [pow_succ', mul_comm]

set_option maxHeartbeats 3000000 in
-- Exact torsion compares the unit-scaled and cyclotomic annihilator ideals.
/-- The source conjugate has exact level `n + 1` at the distinguished
cyclotomic root.  Multiplying the uniformizer by a unit does not change the
annihilator ideal. -/
theorem conjugate_exact_level
    (n : ℕ) (u : ℤ_[p]ˣ) :
    let D := cyclotomicLubinDatum p
    let hI := padic_cyclotomic_adic p k n
    let rhoW : W p k →+* B p k n := algebraMap (W p k) (B p k n)
    let fW := PowerSeries.map (padicIntWitt p k)
      (D.f : PowerSeries ℤ_[p])
    let U := PowerSeries.map (padicIntWitt p k)
      (padicBinomialEndomorphism p (u : ℤ_[p]))
    let sourceB := PowerSeries.map rhoW (PowerSeries.subst fW U)
    let hsource0 : constantCoeff sourceB = 0 := by
      have hfW0 : constantCoeff fW = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
        rw [show coeff 0 (D.f : PowerSeries ℤ_[p]) = 0 by
          simpa only [← coeff_zero_eq_constantCoeff_apply] using
            D.lubinTateSeries.1, map_zero]
      have hU0 : constantCoeff U = 0 := by
        rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
          coeff_zero_eq_constantCoeff_apply,
          endomorphism_constant_coeff, map_zero]
      have hs0 : constantCoeff (PowerSeries.subst fW U) = 0 :=
        PowerSeries.constantCoeff_subst_eq_zero hfW0 U hU0
      rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        coeff_zero_eq_constantCoeff_apply, hs0, map_zero]
    let rootI := FGLaw.APts.toIdeal hI
      ((lubinFormalLaw D.pi D.pi_irreducible.ne_zero
        D.pi_irreducible.not_isUnit (padic_int_field p)
        (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map
          (padicWittRing p k n))
      (padicCyclotomicPoint p k n)
    (seriesAdic hI sourceB hsource0)^[n + 1] rootI = 0 ∧
      (seriesAdic hI sourceB hsource0)^[n] rootI ≠ 0 := by
  dsimp only
  let D := cyclotomicLubinDatum p
  let hI := padic_cyclotomic_adic p k n
  let rhoW : W p k →+* B p k n := algebraMap (W p k) (B p k n)
  let fW := PowerSeries.map (padicIntWitt p k)
    (D.f : PowerSeries ℤ_[p])
  let U := PowerSeries.map (padicIntWitt p k)
    (padicBinomialEndomorphism p (u : ℤ_[p]))
  let sourceB := PowerSeries.map rhoW (PowerSeries.subst fW U)
  have hsource0 : constantCoeff sourceB = 0 := by
    have hfW0 : constantCoeff fW = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
      rw [show coeff 0 (D.f : PowerSeries ℤ_[p]) = 0 by
        simpa only [← coeff_zero_eq_constantCoeff_apply] using
          D.lubinTateSeries.1, map_zero]
    have hU0 : constantCoeff U = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        coeff_zero_eq_constantCoeff_apply,
        endomorphism_constant_coeff, map_zero]
    have hs0 : constantCoeff (PowerSeries.subst fW U) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero hfW0 U hU0
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, hs0, map_zero]
  let F := (lubinFormalLaw D.pi D.pi_irreducible.ne_zero
    D.pi_irreducible.not_isUnit (padic_int_field p)
    (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map
      (padicWittRing p k n)
  let z := padicCyclotomicPoint p k n
  let rootI := FGLaw.APts.toIdeal hI F z
  have htors := witt_point_torsion p k n
  change Ideal.torsionOf ℤ_[p] _ z =
      Ideal.span {D.pi ^ (n + 1)} at htors
  have hlevelSmul : (((p : ℤ_[p]) * (u : ℤ_[p])) ^ (n + 1)) • z = 0 := by
    apply (Ideal.mem_torsionOf_iff z
      (((p : ℤ_[p]) * (u : ℤ_[p])) ^ (n + 1))).mp
    rw [htors]
    apply Ideal.mem_span_singleton.mpr
    change (p : ℤ_[p]) ^ (n + 1) ∣
      ((p : ℤ_[p]) * (u : ℤ_[p])) ^ (n + 1)
    rw [mul_pow]
    exact dvd_mul_right _ _
  constructor
  · rw [conjugate_iterate_root p k n u (n + 1)]
    rw [hlevelSmul]
    exact FGLaw.APts.toIdeal_zero hI F
  · intro hzero
    rw [conjugate_iterate_root p k n u n] at hzero
    have hsmul : (((p : ℤ_[p]) * (u : ℤ_[p])) ^ n) • z = 0 := by
      apply (FGLaw.APts.equivIdeal hI F).injective
      simpa only [FGLaw.APts.equivIdeal_apply,
        FGLaw.APts.toIdeal_zero] using hzero
    have hmem : (((p : ℤ_[p]) * (u : ℤ_[p])) ^ n) ∈
        Ideal.span {D.pi ^ (n + 1)} := by
      rw [← htors]
      exact (Ideal.mem_torsionOf_iff z _).mpr hsmul
    have hdiv : D.pi ^ (n + 1) ∣
        ((p : ℤ_[p]) * (u : ℤ_[p])) ^ n :=
      Ideal.mem_span_singleton.mp hmem
    change (p : ℤ_[p]) ^ (n + 1) ∣
      ((p : ℤ_[p]) * (u : ℤ_[p])) ^ n at hdiv
    rw [mul_pow] at hdiv
    have hpdiv : (p : ℤ_[p]) ^ (n + 1) ∣ (p : ℤ_[p]) ^ n :=
      (u.isUnit.pow n).dvd_mul_right.mp hdiv
    have : n + 1 ≤ n :=
      (pow_dvd_pow_iff (padic_int_ne p)
        (padic_int_unit p)).mp hpdiv
    omega

/-- A conjugating series with unit linear coefficient sends the cyclotomic
root to an associate, so it does not change the uniformizer ideal. -/
theorem witt_theta_associated
    (n : ℕ) (epsilon : (W p k)ˣ)
    (theta : PowerSeries (W p k))
    (htheta0 : constantCoeff theta = 0)
    (htheta1 : coeff 1 theta = (epsilon : W p k)) :
    Associated (wittThetaValue p k n theta)
      (cyclotomicWittRoot p k n) := by
  let rho : W p k →+* B p k n := algebraMap (W p k) (B p k n)
  let root := cyclotomicWittRoot p k n
  let hI := padic_cyclotomic_adic p k n
  letI : IsLinearTopology (B p k n) (B p k n) :=
    IsLinearTopology.mk_of_hasBasis (B p k n) hI.hasBasis_nhds_zero
  obtain ⟨h, hh⟩ := PowerSeries.X_dvd_iff.mpr htheta0
  have hh0 : constantCoeff h = (epsilon : W p k) := by
    rw [hh] at htheta1
    simpa [PowerSeries.coeff_one_mul] using htheta1
  let hB := PowerSeries.map rho h
  let z := PowerSeries.eval₂ (RingHom.id (B p k n)) root hB
  have hzunit : IsUnit z := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    rw [padic_witt_maximal p k n]
    intro hz
    let tail := hB - PowerSeries.C (rho (epsilon : W p k))
    have htail0 : constantCoeff tail = 0 := by
      change rho (constantCoeff h) - rho (epsilon : W p k) = 0
      rw [hh0, sub_self]
    have htailmem : PowerSeries.eval₂ (RingHom.id (B p k n)) root tail ∈
        Ideal.span {root} :=
      constant_coeff_adic hI tail
        (Ideal.mem_span_singleton_self root)
        (by rw [htail0]; exact Ideal.zero_mem _)
    have hdiff : z - rho (epsilon : W p k) =
        PowerSeries.eval₂ (RingHom.id (B p k n)) root tail := by
      let ev := PowerSeries.eval₂Hom
        (φ := RingHom.id (B p k n)) (a := root) continuous_id
        (padic_cyclotomic_eval p k n)
      have hev (f : PowerSeries (B p k n)) :
          ev f = PowerSeries.eval₂ (RingHom.id (B p k n)) root f :=
        congrFun (PowerSeries.coe_eval₂Hom continuous_id
          (padic_cyclotomic_eval p k n)) f
      change PowerSeries.eval₂ (RingHom.id (B p k n)) root hB -
          rho (epsilon : W p k) =
        PowerSeries.eval₂ (RingHom.id (B p k n)) root tail
      rw [← hev hB, ← hev tail]
      have hC : ev (PowerSeries.C (rho (epsilon : W p k))) =
          rho (epsilon : W p k) := by
        rw [hev]
        exact PowerSeries.eval₂_C _ _ _
      rw [← hC, ← map_sub]
    have hepsmem : rho (epsilon : W p k) ∈ Ideal.span {root} := by
      have hd := hdiff ▸ htailmem
      have hsub := (Ideal.span {root}).sub_mem hz hd
      simpa only [sub_sub_cancel] using hsub
    have hepsunit : IsUnit (rho (epsilon : W p k)) :=
      RingHom.isUnit_map rho epsilon.isUnit
    exact (IsLocalRing.notMem_maximalIdeal.mpr hepsunit) (by
      rwa [padic_witt_maximal p k n])
  have hy : wittThetaValue p k n theta = root * z := by
    let ev := PowerSeries.eval₂Hom
      (φ := RingHom.id (B p k n)) (a := root) continuous_id
      (padic_cyclotomic_eval p k n)
    have hev (f : PowerSeries (B p k n)) :
        ev f = PowerSeries.eval₂ (RingHom.id (B p k n)) root f :=
      congrFun (PowerSeries.coe_eval₂Hom continuous_id
        (padic_cyclotomic_eval p k n)) f
    change PowerSeries.eval₂ (RingHom.id (B p k n)) root
        (PowerSeries.map rho theta) = root *
      PowerSeries.eval₂ (RingHom.id (B p k n)) root hB
    rw [← hev (PowerSeries.map rho theta), ← hev hB]
    rw [hh, map_mul (PowerSeries.map rho), PowerSeries.map_X]
    change ev (PowerSeries.X * hB) = root * ev hB
    rw [map_mul ev]
    have hX : ev PowerSeries.X = root := by
      rw [hev]
      exact PowerSeries.eval₂_X _ _
    rw [hX]
  rw [hy]
  exact associated_mul_unit_left root z hzunit

set_option maxHeartbeats 4000000 in
-- The final primitive-root construction combines adic evaluation and semilinear fixedness.
/-- The uniformizer-change series sends the cyclotomic root to a primitive
root of the reduced basic Lubin--Tate polynomial, and that root is fixed by
the semilinear Frobenius lift. -/
theorem padic_witt_root
    (n : ℕ) (u : ℤ_[p]ˣ) :
    ∃ y : B p k n,
      Polynomial.eval₂ (padicWittRing p k n) y
          (reducedLubinIterate (padicTateDatum p u).f n) = 0 ∧
        wittFrobeniusLift p k n u y = y ∧
        Associated y (cyclotomicWittRoot p k n) := by
  let D := cyclotomicLubinDatum p
  let G := padicTateDatum p u
  let hI := padic_cyclotomic_adic p k n
  let rhoZ := padicWittRing p k n
  let rhoW : W p k →+* B p k n := algebraMap (W p k) (B p k n)
  let fW := PowerSeries.map (padicIntWitt p k)
    (D.f : PowerSeries ℤ_[p])
  let U := PowerSeries.map (padicIntWitt p k)
    (padicBinomialEndomorphism p (u : ℤ_[p]))
  let sourceW := PowerSeries.subst fW U
  let sourceB := PowerSeries.map rhoW sourceW
  let gW := PowerSeries.map (padicIntWitt p k)
    (G.f : PowerSeries ℤ_[p])
  let gB := PowerSeries.map rhoW gW
  obtain ⟨epsilon, theta, inverseTheta, htheta0, htheta1,
      hinverse0, hthetaInverse, hinverseTheta, hsemilinear,
      hconjugate⟩ :=
    witt_uniformizer_change p k u
  have hconjugate' :
      semilinearConjugate WittVector.frobenius theta inverseTheta fW =
        gW := by
    simpa [D, G, fW, gW, cyclotomicLubinDatum,
      padicCyclotomicLubin, cyclotomicPowerSeries,
      padicTateDatum] using hconjugate
  have hfW0 : constantCoeff fW = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    rw [show coeff 0 (D.f : PowerSeries ℤ_[p]) = 0 by
      simpa only [← coeff_zero_eq_constantCoeff_apply] using
        D.lubinTateSeries.1, map_zero]
  have hU0 : constantCoeff U = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply,
      endomorphism_constant_coeff, map_zero]
  have hsourceW0 : constantCoeff sourceW = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hfW0 U hU0
  have hsourceB0 : constantCoeff sourceB = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, hsourceW0, map_zero]
  have hgW0 : constantCoeff gW = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    rw [show coeff 0 (G.f : PowerSeries ℤ_[p]) = 0 by
      simpa only [← coeff_zero_eq_constantCoeff_apply] using
        G.lubinTateSeries.1, map_zero]
  have hgB0 : constantCoeff gB = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, hgW0, map_zero]
  let thetaB := PowerSeries.map rhoW theta
  let inverseThetaB := PowerSeries.map rhoW inverseTheta
  have hthetaB0 : constantCoeff thetaB = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, htheta0, map_zero]
  have hinverseB0 : constantCoeff inverseThetaB = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, hinverse0, map_zero]
  have hthetaInverseB : PowerSeries.subst inverseThetaB thetaB = X := by
    calc
      PowerSeries.subst inverseThetaB thetaB =
          PowerSeries.map rhoW (PowerSeries.subst inverseTheta theta) :=
        (PowerSeries.map_subst
          (PowerSeries.HasSubst.of_constantCoeff_zero' hinverse0) theta).symm
      _ = X := by rw [hthetaInverse, PowerSeries.map_X]
  have hinverseThetaB : PowerSeries.subst thetaB inverseThetaB = X := by
    calc
      PowerSeries.subst thetaB inverseThetaB =
          PowerSeries.map rhoW (PowerSeries.subst theta inverseTheta) :=
        (PowerSeries.map_subst
          (PowerSeries.HasSubst.of_constantCoeff_zero' htheta0)
          inverseTheta).symm
      _ = X := by rw [hinverseTheta, PowerSeries.map_X]
  have hintertwinesW : PowerSeries.subst theta gW =
      PowerSeries.subst sourceW theta :=
    semilinear_intertwines_theta WittVector.frobenius
      htheta0 hinverse0 hfW0 hU0 hinverseTheta hsemilinear hconjugate'
  have hintertwinesB : PowerSeries.subst thetaB gB =
      PowerSeries.subst sourceB thetaB := by
    calc
      PowerSeries.subst thetaB gB =
          PowerSeries.map rhoW (PowerSeries.subst theta gW) :=
        (PowerSeries.map_subst
          (PowerSeries.HasSubst.of_constantCoeff_zero' htheta0) gW).symm
      _ = PowerSeries.map rhoW (PowerSeries.subst sourceW theta) := by
        rw [hintertwinesW]
      _ = PowerSeries.subst sourceB thetaB :=
        PowerSeries.map_subst
          (PowerSeries.HasSubst.of_constantCoeff_zero' hsourceW0) theta
  let F := (lubinFormalLaw D.pi D.pi_irreducible.ne_zero
    D.pi_irreducible.not_isUnit (padic_int_field p)
    (D.f : PowerSeries ℤ_[p]) D.lubin_tate_card).map rhoZ
  let rootI := FGLaw.APts.toIdeal hI F
    (padicCyclotomicPoint p k n)
  let yI := seriesAdic hI thetaB hthetaB0 rootI
  have hsourceExact :
      (seriesAdic hI sourceB hsourceB0)^[n + 1] rootI = 0 ∧
        (seriesAdic hI sourceB hsourceB0)^[n] rootI ≠ 0 := by
    exact conjugate_exact_level p k n u
  have hiterate (m : ℕ) :
      (seriesAdic hI gB hgB0)^[m] yI =
        seriesAdic hI thetaB hthetaB0
          ((seriesAdic hI sourceB hsourceB0)^[m] rootI) := by
    exact adic_iterate_intertwines hI sourceB gB thetaB
      hsourceB0 hgB0 hthetaB0 hintertwinesB m rootI
  have hgLevel : (seriesAdic hI gB hgB0)^[n + 1] yI = 0 := by
    calc
      (seriesAdic hI gB hgB0)^[n + 1] yI =
          seriesAdic hI thetaB hthetaB0
            ((seriesAdic hI sourceB hsourceB0)^[n + 1] rootI) :=
        hiterate (n + 1)
      _ = seriesAdic hI thetaB hthetaB0 0 := by
        rw [hsourceExact.1]
      _ = 0 := series_adic_zero hI thetaB hthetaB0
  have hgPrimitive : (seriesAdic hI gB hgB0)^[n] yI ≠ 0 := by
    intro hgzero
    have hthetaSource : seriesAdic hI thetaB hthetaB0
        ((seriesAdic hI sourceB hsourceB0)^[n] rootI) = 0 := by
      rw [← hiterate n]
      exact hgzero
    let e := powerSeriesAdic hI thetaB inverseThetaB hthetaB0
      hinverseB0 hthetaInverseB hinverseThetaB
    apply hsourceExact.2
    apply e.injective
    change seriesAdic hI thetaB hthetaB0
        ((seriesAdic hI sourceB hsourceB0)^[n] rootI) =
      seriesAdic hI thetaB hthetaB0 0
    rw [hthetaSource, series_adic_zero]
  have hgLevelEval : PowerSeries.eval₂ (RingHom.id (B p k n)) (yI : B p k n)
      (substitutionIterate gB (n + 1)) = 0 := by
    have hiter := adic_iterate_substitution
      hI gB hgB0 (n + 1) yI
    have hiter' := congrArg Subtype.val hiter
    rw [hgLevel] at hiter'
    exact hiter'.symm
  have hgPrimitiveEval : PowerSeries.eval₂ (RingHom.id (B p k n))
      (yI : B p k n) (substitutionIterate gB n) ≠ 0 := by
    intro heval
    apply hgPrimitive
    have hiter := adic_iterate_substitution
      hI gB hgB0 n yI
    apply Subtype.ext
    simpa only [coe_series_adic, heval] using
      congrArg Subtype.val hiter
  have hgMap : gB = PowerSeries.map rhoZ (G.f : PowerSeries ℤ_[p]) := by
    apply PowerSeries.ext
    intro i
    rfl
  rw [hgMap] at hgLevelEval hgPrimitiveEval
  have hG0 : G.f.coeff 0 = 0 := by
    simpa using G.lubinTateSeries.1
  rw [eval₂_substitutionIterate_map_polynomial rhoZ G.f hG0
      (n + 1) (yI : B p k n)] at hgLevelEval
  rw [eval₂_substitutionIterate_map_polynomial rhoZ G.f hG0
      n (yI : B p k n)] at hgPrimitiveEval
  let gPoly := G.f.map rhoZ
  have hmapIter (m : ℕ) :
      (G.f.comp^[m] Polynomial.X).map rhoZ =
        gPoly.comp^[m] Polynomial.X := by
    induction m with
    | zero => simp [gPoly]
    | succ m ih =>
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          Polynomial.map_comp, ih]
  have hgLevel' : (fun z ↦ gPoly.eval z)^[n + 1] (yI : B p k n) = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, hmapIter,
      Polynomial.iterate_comp_eval] at hgLevelEval
    simpa using hgLevelEval
  have hgPrimitive' : (fun z ↦ gPoly.eval z)^[n] (yI : B p k n) ≠ 0 := by
    rw [Polynomial.eval₂_eq_eval_map, hmapIter,
      Polynomial.iterate_comp_eval] at hgPrimitiveEval
    simpa using hgPrimitiveEval
  have hgRoot : gPoly.eval ((fun z ↦ gPoly.eval z)^[n]
      (yI : B p k n)) = 0 := by
    simpa only [Function.iterate_succ_apply'] using hgLevel'
  have hgPoly0 : gPoly.coeff 0 = 0 := by
    simp [gPoly, hG0]
  have hrootMapped : (reducedLubinIterate gPoly n).eval
      (yI : B p k n) = 0 :=
    reduced_tate_iterate gPoly hgPoly0 n
      (yI : B p k n) hgPrimitive' hgRoot
  have hroot : Polynomial.eval₂ rhoZ (yI : B p k n)
      (reducedLubinIterate G.f n) = 0 := by
    simpa [Polynomial.eval₂_eq_eval_map, gPoly,
      lubin_tate_iterate] using hrootMapped
  have hy : (yI : B p k n) =
      wittThetaValue p k n theta := by
    rfl
  refine ⟨wittThetaValue p k n theta, ?_, ?_, ?_⟩
  · rw [← hy]
    exact hroot
  · exact witt_theta_value
      p k n u theta htheta0 hsemilinear
  · exact witt_theta_associated
      p k n epsilon theta htheta0 htheta1

/-- On the residue field of the Witt-root DVR, the semilinear lift is the
arithmetic Frobenius. -/
theorem padic_witt_lift
    (n : ℕ) (u : ℤ_[p]ˣ) :
    (padicWittResidue p k n).comp
        (wittFrobeniusLift p k n u) =
      (frobenius k p).comp (padicWittResidue p k n) := by
  apply AdjoinRoot.ringHom_ext
  · apply RingHom.ext
    intro a
    change padicWittResidue p k n
        (wittFrobeniusLift p k n u
          (algebraMap (W p k) (B p k n) a)) =
      frobenius k p
        (padicWittResidue p k n
          (algebraMap (W p k) (B p k n) a))
    rw [padic_witt_coeff]
    simp only [padicWittResidue, frobenius_def]
    simp [WittVector.coeff_frobenius_charP]
  · change padicWittResidue p k n
        (wittFrobeniusLift p k n u
          (cyclotomicWittRoot p k n)) =
      frobenius k p
        (padicWittResidue p k n
          (cyclotomicWittRoot p k n))
    rw [padic_frobenius_root]
    have hroot : padicWittResidue p k n
        (cyclotomicWittRoot p k n) = 0 := by
      exact AdjoinRoot.lift_root _
    rw [hroot, map_zero]
    rw [← RingHom.mem_ker, padic_witt_ker]
    exact padic_cyclotomic_witt p k n u⁻¹

/-- Proposition I.3.10 supplies, for every unit, a conjugating series whose
value at the finite cyclotomic root is fixed by the semilinear Frobenius
lift. -/
theorem padic_theta_value
    (n : ℕ) (u : ℤ_[p]ˣ) :
    ∃ (epsilon : (W p k)ˣ)
      (theta inverseTheta : PowerSeries (W p k)),
      constantCoeff theta = 0 ∧
      coeff 1 theta = (epsilon : W p k) ∧
      constantCoeff inverseTheta = 0 ∧
      PowerSeries.subst inverseTheta theta = X ∧
      PowerSeries.subst theta inverseTheta = X ∧
      wittFrobeniusLift p k n u
          (wittThetaValue p k n theta) =
        wittThetaValue p k n theta := by
  obtain ⟨epsilon, theta, inverseTheta, htheta0, htheta1,
      hinverse0, hthetaInverse, hinverseTheta, hsemilinear, _⟩ :=
    witt_uniformizer_change p k u
  exact ⟨epsilon, theta, inverseTheta, htheta0, htheta1, hinverse0,
    hthetaInverse, hinverseTheta,
    witt_theta_value
      p k n u theta htheta0 hsemilinear⟩

/-- A canonical primitive root of the basic Lubin--Tate polynomial for the
uniformizer `p * u`, chosen inside the common Witt-root algebra. -/
noncomputable def padicWittRoot (n : ℕ) (u : ℤ_[p]ˣ) :
    B p k n :=
  Classical.choose
    (padic_witt_root p k n u)

@[simp]
theorem padic_witt_reduced
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Polynomial.eval₂ (padicWittRing p k n)
        (padicWittRoot p k n u)
        (reducedLubinIterate (padicTateDatum p u).f n) = 0 :=
  (Classical.choose_spec
    (padic_witt_root p k n u)).1

@[simp]
theorem witt_frobenius_root
    (n : ℕ) (u : ℤ_[p]ˣ) :
    wittFrobeniusLift p k n u
        (padicWittRoot p k n u) =
      padicWittRoot p k n u :=
  (Classical.choose_spec
    (padic_witt_root p k n u)).2.1

/-- The chosen basic root is associated to the distinguished cyclotomic
root in the common complete DVR. -/
theorem padic_witt_associated
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Associated (padicWittRoot p k n u)
      (cyclotomicWittRoot p k n) :=
  (Classical.choose_spec
    (padic_witt_root p k n u)).2.2

/-- The chosen basic root satisfies the scalar-extended reduced polynomial
in the common Witt fraction field. -/
theorem padic_witt_basic₂_reduced_eq_zero
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Polynomial.eval₂ (wittRootFraction p k n)
      (algebraMap (B p k n) (C p k n)
        (padicWittRoot p k n u))
      ((reducedLubinIterate
        (padicTateDatum p u).f n).map
          (algebraMap ℤ_[p] ℚ_[p])) = 0 := by
  let G := padicTateDatum p u
  let y := padicWittRoot p k n u
  change Polynomial.eval₂ (wittRootFraction p k n)
      (algebraMap (B p k n) (C p k n) y)
      ((reducedLubinIterate G.f n).map
        (algebraMap ℤ_[p] ℚ_[p])) = 0
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
      (Polynomial.eval₂ (padicWittRing p k n) y
        (reducedLubinIterate G.f n)) = 0
  rw [padic_witt_reduced, map_zero]

/-- The basic `p * u` Lubin--Tate root field embedded in the same Witt
fraction field as the cyclotomic `p`-Lubin--Tate root field. -/
def wittFractionAlg (n : ℕ) (u : ℤ_[p]ˣ) :
    (padicTateDatum p u).RootField ℚ_[p] n →ₐ[ℚ_[p]]
      C p k n :=
  AdjoinRoot.liftAlgHom
    ((padicTateDatum p u).reducedPolynomial ℚ_[p] n)
    (Algebra.ofId ℚ_[p] (C p k n))
    (algebraMap (B p k n) (C p k n)
      (padicWittRoot p k n u))
    (by
      simpa [Polynomial.aeval_def] using
        padic_witt_basic₂_reduced_eq_zero p k n u)

@[simp]
theorem witt_fraction_alg
    (n : ℕ) (u : ℤ_[p]ˣ) :
    wittFractionAlg p k n u
        ((padicTateDatum p u).root ℚ_[p] n) =
      algebraMap (B p k n) (C p k n)
        (padicWittRoot p k n u) := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The semilinear Frobenius/unit automorphism fixes the embedded basic
`p * u` Lubin--Tate root field pointwise. -/
theorem witt_fraction_restrict
    (n : ℕ) (u : ℤ_[p]ˣ) :
    (wittFractionFrobenius p k n u).toAlgHom.comp
        (wittFractionAlg p k n u) =
      wittFractionAlg p k n u := by
  apply AdjoinRoot.algHom_ext
  let root := (padicTateDatum p u).root ℚ_[p] n
  calc
    ((wittFractionFrobenius p k n u).toAlgHom.comp
        (wittFractionAlg p k n u)) root =
        wittFractionFrobenius p k n u
          (wittFractionAlg p k n u root) := rfl
    _ = algebraMap (B p k n) (C p k n)
          (padicWittRoot p k n u) := by
      rw [witt_fraction_alg]
      change padicFractionFrobenius p k n u
          (algebraMap (B p k n) (C p k n)
            (padicWittRoot p k n u)) = _
      rw [witt_fraction_algebra,
        witt_frobenius_root]
    _ = wittFractionAlg p k n u root := by
      rw [witt_fraction_alg]

/-- The embedded finite cyclotomic `p`-Lubin--Tate root field. -/
def padicWittIntermediate (n : ℕ) :
    IntermediateField ℚ_[p] (C p k n) :=
  (padicWittFraction p k n).fieldRange

/-- The embedded finite basic `p * u` Lubin--Tate root field. -/
def padicCyclotomicIntermediate (n : ℕ) (u : ℤ_[p]ˣ) :
    IntermediateField ℚ_[p] (C p k n) :=
  (wittFractionAlg p k n u).fieldRange

/-- The abstract cyclotomic root field is canonically equivalent to its
embedded field range. -/
noncomputable def padicWittEquiv (n : ℕ) :
    (cyclotomicLubinDatum p).RootField ℚ_[p] n ≃ₐ[ℚ_[p]]
      padicWittIntermediate p k n := by
  let f := padicWittFraction p k n
  simpa [padicWittIntermediate,
    AlgHom.fieldRange_toSubalgebra f] using
      (AlgEquiv.ofInjectiveField f)

/-- The abstract basic root field is canonically equivalent to its embedded
field range. -/
noncomputable def padicWittBasic
    (n : ℕ) (u : ℤ_[p]ˣ) :
    (padicTateDatum p u).RootField ℚ_[p] n ≃ₐ[ℚ_[p]]
      padicCyclotomicIntermediate p k n u := by
  let f := wittFractionAlg p k n u
  simpa [padicCyclotomicIntermediate,
    AlgHom.fieldRange_toSubalgebra f] using
      (AlgEquiv.ofInjectiveField f)

noncomputable instance padicWittDimensional
    (n : ℕ) :
    FiniteDimensional ℚ_[p]
      (padicWittIntermediate p k n) :=
  Module.Finite.equiv
    (padicWittEquiv p k n).toLinearEquiv

noncomputable instance padicCyclotomicDimensional
    (n : ℕ) (u : ℤ_[p]ˣ) :
    FiniteDimensional ℚ_[p]
      (padicCyclotomicIntermediate p k n u) :=
  Module.Finite.equiv
    (padicWittBasic p k n u).toLinearEquiv

noncomputable instance padicWittGalois
    (n : ℕ) :
    IsGalois ℚ_[p]
      (padicWittIntermediate p k n) :=
  IsGalois.of_algEquiv
    (padicWittEquiv p k n)

noncomputable instance cyclotomicWittGalois
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsGalois ℚ_[p]
      (padicCyclotomicIntermediate p k n u) :=
  IsGalois.of_algEquiv (padicWittBasic p k n u)

/-- The finite compositum in which the uniformizer-change comparison takes
place. -/
def wittComparisonCompositum (n : ℕ) (u : ℤ_[p]ˣ) :
    IntermediateField ℚ_[p] (C p k n) :=
  padicWittIntermediate p k n ⊔
    padicCyclotomicIntermediate p k n u

noncomputable instance comparisonCompositumDimensional
    (n : ℕ) (u : ℤ_[p]ˣ) :
    FiniteDimensional ℚ_[p]
      (wittComparisonCompositum p k n u) :=
  IntermediateField.finiteDimensional_sup
    (padicWittIntermediate p k n)
    (padicCyclotomicIntermediate p k n u)

set_option maxHeartbeats 3000000 in
-- The two embedded Galois structures and their supremum elaborate together.
set_option synthInstance.maxHeartbeats 500000 in
noncomputable instance comparisonCompositumGalois
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsGalois ℚ_[p]
      (wittComparisonCompositum p k n u) := by
  let E := padicWittIntermediate p k n
  let F := padicCyclotomicIntermediate p k n u
  letI : Normal ℚ_[p] E := IsGalois.to_normal
  letI : Normal ℚ_[p] F := IsGalois.to_normal
  letI : Algebra.IsSeparable ℚ_[p] E := IsGalois.to_isSeparable
  letI : Algebra.IsSeparable ℚ_[p] F := IsGalois.to_isSeparable
  change IsGalois ℚ_[p] (E ⊔ F : IntermediateField ℚ_[p] (C p k n))
  exact
    { to_normal := inferInstance
      to_isSeparable := inferInstance }

/-- The cyclotomic root field embedded directly into the finite comparison
compositum. -/
def padicWittComparison
    (n : ℕ) (u : ℤ_[p]ˣ) :
    (cyclotomicLubinDatum p).RootField ℚ_[p] n →ₐ[ℚ_[p]]
      wittComparisonCompositum p k n u :=
  (padicWittFraction p k n).codRestrict
    (wittComparisonCompositum p k n u).toSubalgebra (fun z ↦ by
      change padicWittFraction p k n z ∈
        wittComparisonCompositum p k n u
      apply (show padicWittIntermediate p k n ≤
          wittComparisonCompositum p k n u by
        rw [wittComparisonCompositum]
        exact le_sup_left)
      exact (AlgHom.mem_fieldRange
          (f := padicWittFraction p k n)).2
        ⟨z, rfl⟩)

@[simp]
theorem witt_comparison_coe
    (n : ℕ) (u : ℤ_[p]ˣ)
    (z : (cyclotomicLubinDatum p).RootField ℚ_[p] n) :
    (padicWittComparison p k n u z : C p k n) =
      padicWittFraction p k n z :=
  rfl

/-- The basic `p * u` root field embedded directly into the finite
comparison compositum. -/
def wittComparisonAlg
    (n : ℕ) (u : ℤ_[p]ˣ) :
    (padicTateDatum p u).RootField ℚ_[p] n →ₐ[ℚ_[p]]
      wittComparisonCompositum p k n u :=
  (wittFractionAlg p k n u).codRestrict
    (wittComparisonCompositum p k n u).toSubalgebra (fun z ↦ by
      change wittFractionAlg p k n u z ∈
        wittComparisonCompositum p k n u
      apply (show padicCyclotomicIntermediate p k n u ≤
          wittComparisonCompositum p k n u by
        rw [wittComparisonCompositum]
        exact le_sup_right)
      exact (AlgHom.mem_fieldRange
          (f := wittFractionAlg p k n u)).2
        ⟨z, rfl⟩)

@[simp]
theorem padic_comparison_coe
    (n : ℕ) (u : ℤ_[p]ˣ)
    (z : (padicTateDatum p u).RootField ℚ_[p] n) :
    (wittComparisonAlg p k n u z : C p k n) =
      wittFractionAlg p k n u z :=
  rfl

/-- The ambient semilinear automorphism preserves the embedded cyclotomic
root field. -/
theorem witt_fraction_frobenius
    (n : ℕ) (u : ℤ_[p]ˣ) :
    (padicWittIntermediate p k n).map
        (wittFractionFrobenius p k n u).toAlgHom =
      padicWittIntermediate p k n := by
  rw [padicWittIntermediate,
    AlgHom.map_fieldRange,
    padic_fraction_restrict]
  apply SetLike.ext
  intro z
  rw [AlgHom.mem_fieldRange, AlgHom.mem_fieldRange]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨padicCyclotomicOrbit p n
      (padicIntInteger p (n + 1) u⁻¹) x, rfl⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ :=
      (padicCyclotomicOrbit p n
        (padicIntInteger p (n + 1) u⁻¹)).surjective y
    exact ⟨x, rfl⟩

/-- The ambient semilinear automorphism fixes the embedded basic root field,
so in particular it preserves it. -/
theorem padic_fraction_frobenius
    (n : ℕ) (u : ℤ_[p]ˣ) :
    (padicCyclotomicIntermediate p k n u).map
        (wittFractionFrobenius p k n u).toAlgHom =
      padicCyclotomicIntermediate p k n u := by
  rw [padicCyclotomicIntermediate,
    AlgHom.map_fieldRange,
    witt_fraction_restrict]

/-- Hence the ambient semilinear automorphism preserves the finite
comparison compositum. -/
theorem witt_fraction_compositum
    (n : ℕ) (u : ℤ_[p]ˣ) :
    (wittComparisonCompositum p k n u).map
        (wittFractionFrobenius p k n u).toAlgHom =
      wittComparisonCompositum p k n u := by
  rw [wittComparisonCompositum,
    IntermediateField.map_sup,
    witt_fraction_frobenius,
    padic_fraction_frobenius]

/-- The restriction of the Witt Frobenius/unit automorphism to the finite
comparison compositum. -/
noncomputable def comparisonCompositumFrobenius
    (n : ℕ) (u : ℤ_[p]ˣ) :
    wittComparisonCompositum p k n u ≃ₐ[ℚ_[p]]
      wittComparisonCompositum p k n u :=
  (IntermediateField.equivMap
      (wittComparisonCompositum p k n u)
      (wittFractionFrobenius p k n u).toAlgHom).trans
    (IntermediateField.equivOfEq
      (witt_fraction_compositum p k n u))

@[simp]
theorem comparison_compositum_coe
    (n : ℕ) (u : ℤ_[p]ˣ)
    (x : wittComparisonCompositum p k n u) :
    (comparisonCompositumFrobenius p k n u x :
      C p k n) =
      wittFractionFrobenius p k n u x :=
  rfl

/-- The embedded basic root field, now regarded as an intermediate field of
the finite comparison compositum. -/
def padicCyclotomicComparison
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IntermediateField ℚ_[p]
      (wittComparisonCompositum p k n u) :=
  (padicCyclotomicIntermediate p k n u).restrict le_sup_right

noncomputable instance wittComparisonBasic
    (n : ℕ) (u : ℤ_[p]ˣ) :
    Algebra (padicCyclotomicComparison p k n u)
      (wittComparisonCompositum p k n u) :=
  (padicCyclotomicComparison p k n u).toAlgebra

/-- Restricting the ambient basic field to the comparison compositum does
not change it. -/
noncomputable def padicCyclotomicWitt
    (n : ℕ) (u : ℤ_[p]ˣ) :
    padicCyclotomicIntermediate p k n u ≃ₐ[ℚ_[p]]
      padicCyclotomicComparison p k n u :=
  IntermediateField.restrict_algEquiv le_sup_right

noncomputable instance
    padicComparisonDimensional
    (n : ℕ) (u : ℤ_[p]ˣ) :
    FiniteDimensional ℚ_[p]
      (padicCyclotomicComparison p k n u) :=
  Module.Finite.equiv
    (padicCyclotomicWitt p k n u).toLinearEquiv

noncomputable instance padicComparisonGalois
    (n : ℕ) (u : ℤ_[p]ˣ) :
    IsGalois ℚ_[p]
      (padicCyclotomicComparison p k n u) :=
  IsGalois.of_algEquiv
    (padicCyclotomicWitt p k n u)

/-- The comparison Frobenius fixes every element of the embedded basic root
field. -/
theorem comparison_compositum_fix
    (n : ℕ) (u : ℤ_[p]ˣ)
    (x : padicCyclotomicComparison p k n u) :
    comparisonCompositumFrobenius p k n u x.1 = x.1 := by
  apply Subtype.ext
  change wittFractionFrobenius p k n u
      ((x.1 : wittComparisonCompositum p k n u) : C p k n) =
    ((x.1 : wittComparisonCompositum p k n u) : C p k n)
  let f := wittFractionAlg p k n u
  have hx : ((x.1 : wittComparisonCompositum p k n u) :
      C p k n) ∈ padicCyclotomicIntermediate p k n u := by
    exact (IntermediateField.mem_restrict le_sup_right x.1).1 x.property
  obtain ⟨z, hz⟩ := (AlgHom.mem_fieldRange (f := f)).1 hx
  rw [← hz]
  exact DFunLike.congr_fun
    (witt_fraction_restrict
      p k n u) z

/-- The ambient semilinear automorphism, restricted to the comparison
compositum, is an automorphism over the fixed basic root field. -/
noncomputable def wittComparisonFrobenius
    (n : ℕ) (u : ℤ_[p]ˣ) :
    wittComparisonCompositum p k n u ≃ₐ[
      padicCyclotomicComparison p k n u]
      wittComparisonCompositum p k n u :=
  { (comparisonCompositumFrobenius p k n u).toRingEquiv with
    commutes' := fun x ↦
      comparison_compositum_fix p k n u x }

@[simp]
theorem padic_witt_coe
    (n : ℕ) (u : ℤ_[p]ˣ)
    (x : wittComparisonCompositum p k n u) :
    wittComparisonFrobenius p k n u x =
      comparisonCompositumFrobenius p k n u x :=
  rfl

/-- On the cyclotomic root field, the relative comparison Frobenius is the
explicit inverse-unit Lubin--Tate automorphism. -/
theorem witt_comparison_restrict
    (n : ℕ) (u : ℤ_[p]ˣ) :
    ((wittComparisonFrobenius p k n u).toAlgHom
        |>.restrictScalars ℚ_[p]).comp
        (padicWittComparison p k n u) =
      (padicWittComparison p k n u).comp
        (padicCyclotomicOrbit p n
          (padicIntInteger p (n + 1) u⁻¹)).toAlgHom := by
  apply DFunLike.ext _ _
  intro z
  apply Subtype.ext
  exact DFunLike.congr_fun
    (padic_fraction_restrict
      p k n u) z

/-- On the basic `p * u` root field, the relative comparison Frobenius is
the identity. -/
theorem padic_restrict_basic
    (n : ℕ) (u : ℤ_[p]ˣ) :
    ((wittComparisonFrobenius p k n u).toAlgHom
        |>.restrictScalars ℚ_[p]).comp
        (wittComparisonAlg p k n u) =
      wittComparisonAlg p k n u := by
  apply DFunLike.ext _ _
  intro z
  apply Subtype.ext
  exact DFunLike.congr_fun
    (witt_fraction_restrict
      p k n u) z

end

end Submission.CField.LTate

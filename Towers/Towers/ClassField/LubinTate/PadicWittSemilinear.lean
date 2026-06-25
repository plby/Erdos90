import Mathlib.RingTheory.WittVector.Compare
import Mathlib.RingTheory.WittVector.FrobeniusFractionField
import Towers.ClassField.FormalGroups.PowerSeriesUnary
import Towers.ClassField.LubinTate.WittFrobeniusDifference
import Towers.ClassField.LubinTate.PadicCyclotomic
import Towers.ClassField.LubinTate.SemilinearIntertwiningError

/-!
# The semilinear cyclotomic series over the completed unramified integers

For an algebraically closed field `k` of characteristic `p`, `W(k)` is the
valuation ring of the completed maximal unramified extension of `Q_p`.
This file supplies the two arithmetic inputs in Step 1 of Proposition I.3.10:
Frobenius minus the identity is onto, and every Witt-vector unit has a
multiplicative Frobenius eigenvector.  Consequently the semilinear series
intertwining a unit change of uniformizer exists over `W(k)`.
-/

namespace Towers.CField.LTate

open PowerSeries

noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]

/-- The canonical coefficient embedding `Z_p → W(k)`. -/
noncomputable def padicIntWitt : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
    (WittVector.equiv p).symm.toRingHom

omit [IsAlgClosed k] in
/-- Witt Frobenius fixes the embedded copy of `Z_p`. -/
theorem frobenius_int_witt (a : ℤ_[p]) :
    WittVector.frobenius (padicIntWitt p k a) =
      padicIntWitt p k a := by
  apply WittVector.ext
  intro n
  simp only [padicIntWitt, RingHom.coe_comp, Function.comp_apply,
    WittVector.coeff_frobenius_charP, WittVector.map_coeff]
  rw [← map_pow, ZMod.pow_card]

omit [IsAlgClosed k] in
/-- The Frobenius-fixed Witt vectors are exactly the embedded `p`-adic
integers.  This is the kernel assertion in Lemma I.3.11. -/
theorem int_witt_frobenius
    (x : WittVector p k) (hx : WittVector.frobenius x = x) :
    ∃ a : ℤ_[p], padicIntWitt p k a = x := by
  have hcoeff (n : ℕ) : x.coeff n ^ p = x.coeff n := by
    have h := congrArg (fun y : WittVector p k ↦ y.coeff n) hx
    simpa only [WittVector.coeff_frobenius_charP] using h
  have hmem (n : ℕ) : x.coeff n ∈ (⊥ : Subfield k) :=
    (Subfield.mem_bot_iff_pow_eq_self (F := k) (p := p)).2 (hcoeff n)
  choose z hz using fun n ↦
    (show ∃ z : ZMod p, (ZMod.castHom (dvd_refl p) k) z = x.coeff n by
      rw [← RingHom.mem_fieldRange]
      simpa only [ZMod.fieldRange_castHom_eq_bot] using hmem n)
  let y : WittVector p (ZMod p) := WittVector.mk p z
  let a : ℤ_[p] := WittVector.equiv p y
  refine ⟨a, ?_⟩
  change WittVector.map (ZMod.castHom (dvd_refl p) k)
      ((WittVector.equiv p).symm a) = x
  rw [show (WittVector.equiv p).symm a = y by
    exact (WittVector.equiv p).symm_apply_apply y]
  apply WittVector.ext
  intro n
  simpa only [y, WittVector.map_coeff, WittVector.coeff_mk] using hz n

private theorem coeff_zmod_trunc (z : ZMod (p ^ 1)) :
    TruncatedWittVector.coeff (0 : Fin 1)
      (TruncatedWittVector.zmodEquivTrunc p 1 z) =
      ZMod.castHom (by simp) (ZMod p) z := by
  obtain ⟨m, rfl⟩ := ZMod.natCast_zmod_surjective z
  rw [TruncatedWittVector.zmodEquivTrunc_apply, map_natCast, map_natCast]
  change ((m : WittVector p (ZMod p)).coeff 0) = (m : ZMod p)
  change (WittVector.constantCoeff : WittVector p (ZMod p) →+* ZMod p) m = _
  rw [map_natCast]

omit [IsAlgClosed k] in
/-- The zeroth Witt coefficient of the embedded `p`-adic integer is its
reduction modulo `p`. -/
theorem coeff_int_witt (a : ℤ_[p]) :
    (padicIntWitt p k a).coeff 0 =
      ZMod.castHom (by simp) k (PadicInt.toZModPow 1 a) := by
  change (WittVector.map (ZMod.castHom (dvd_refl p) k)
    ((WittVector.equiv p).symm a)).coeff 0 = _
  rw [WittVector.map_coeff]
  change ZMod.castHom (dvd_refl p) k
      ((WittVector.fromPadicInt p a).coeff 0) = _
  have h := WittVector.truncate_lift (p := p) 1
    (WittVector.zmodEquivTrunc_compat p) a
  have hc := congrArg (TruncatedWittVector.coeff (0 : Fin 1)) h
  rw [WittVector.coeff_truncate] at hc
  have hc' : ((WittVector.fromPadicInt p a).coeff 0) =
      TruncatedWittVector.coeff 0
        (TruncatedWittVector.zmodEquivTrunc p 1
          (PadicInt.toZModPow 1 a)) := by
    simpa [WittVector.fromPadicInt] using hc
  rw [hc', coeff_zmod_trunc p]
  obtain ⟨m, hm⟩ := ZMod.natCast_zmod_surjective
    (PadicInt.toZModPow 1 a)
  rw [← hm]
  simp

omit [IsAlgClosed k] in
/-- Coefficientwise descent: a power series over `W(k)` fixed by Witt
Frobenius comes from a power series over `Z_p`. -/
theorem padic_frobenius_fixed
    (f : PowerSeries (WittVector p k))
    (hf : PowerSeries.map WittVector.frobenius f = f) :
    ∃ g : PowerSeries ℤ_[p], PowerSeries.map (padicIntWitt p k) g = f := by
  have hcoeff (n : ℕ) : WittVector.frobenius (PowerSeries.coeff n f) =
      PowerSeries.coeff n f := by
    have h := congrArg (PowerSeries.coeff n) hf
    simpa only [PowerSeries.coeff_map] using h
  choose a ha using fun n ↦
    int_witt_frobenius p k (PowerSeries.coeff n f) (hcoeff n)
  refine ⟨PowerSeries.mk a, ?_⟩
  apply PowerSeries.ext
  intro n
  simpa only [PowerSeries.coeff_map, PowerSeries.coeff_mk] using ha n

/-- The same coefficient embedding in the valuation-integer presentation
used by the generic Lubin--Tate development. -/
noncomputable def normIntegerWitt :
    Valuation.integer (NormedField.valuation (K := ℚ_[p])) →+*
      WittVector p k :=
  (padicIntWitt p k).comp
    (padicNormInt p).toRingHom

omit [IsAlgClosed k] in
/-- Witt Frobenius fixes the transported valuation integers. -/
theorem frobenius_integer_witt
    (a : Valuation.integer (NormedField.valuation (K := ℚ_[p]))) :
    WittVector.frobenius (normIntegerWitt p k a) =
      normIntegerWitt p k a := by
  exact frobenius_int_witt p k
    (padicNormInt p a)

/-- Multiplicative form of Lang surjectivity for Witt Frobenius: for every
unit `u`, there is a unit `epsilon` with `F(epsilon) = epsilon * u`. -/
theorem witt_frobenius_eigenunit
    (u : (WittVector p k)ˣ) :
    ∃ epsilon : (WittVector p k)ˣ,
      WittVector.frobenius (epsilon : WittVector p k) =
        (epsilon : WittVector p k) * (u : WittVector p k) := by
  have h1 : (1 : WittVector p k).coeff 0 ≠ 0 := by simp
  have hu : ((u : WittVector p k).coeff 0) ≠ 0 := by
    exact IsUnit.ne_zero
      ((WittVector.constantCoeff : WittVector p k →+* k).isUnit_map u.isUnit)
  let b := WittVector.frobeniusRotation p h1 hu
  have hb0 : b.coeff 0 ≠ 0 := by
    dsimp only [b, WittVector.frobeniusRotation, WittVector.coeff_mk,
      WittVector.frobeniusRotationCoeff]
    simpa only [WittVector.frobeniusRotationCoeff] using
      (WittVector.RecursionBase.solution_nonzero p h1 hu)
  let hbunit : IsUnit b := WittVector.isUnit_of_coeff_zero_ne_zero b hb0
  let epsilon : (WittVector p k)ˣ := hbunit.unit
  refine ⟨epsilon, ?_⟩
  rw [hbunit.unit_spec]
  simpa only [mul_one] using
    (WittVector.frobenius_frobeniusRotation p h1 hu)

/-- Proposition I.3.10, Step 1, for the completed maximal-unramified
coefficient ring of `Q_p`. -/
theorem padic_semilinear_theta
    (u : (WittVector p k)ˣ) (U : PowerSeries (WittVector p k))
    (hU0 : constantCoeff U = 0) (hU1 : coeff 1 U = (u : WittVector p k)) :
    ∃ (epsilon : (WittVector p k)ˣ) (theta : PowerSeries (WittVector p k)),
      constantCoeff theta = 0 ∧
      coeff 1 theta = (epsilon : WittVector p k) ∧
      PowerSeries.map WittVector.frobenius theta = subst U theta := by
  obtain ⟨epsilon, hepsilon⟩ := witt_frobenius_eigenunit p k u
  obtain ⟨theta, htheta0, htheta1, htheta⟩ :=
    SIStep.exists_semilinearTheta
      WittVector.frobenius epsilon u U hepsilon
      (WittVector.frobenius_sub_surjective p) hU0 hU1
  exact ⟨epsilon, theta, htheta0, htheta1, htheta⟩

end

end Towers.CField.LTate

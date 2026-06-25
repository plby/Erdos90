import Towers.ClassField.LubinTate.PadicWittSemilinear
import Towers.ClassField.LubinTate.UnaryBridge
import Towers.ClassField.LubinTate.FrobeniusReduction

/-!
# Changing the cyclotomic Lubin--Tate uniformizer over Witt vectors

This is Proposition I.3.10 for `Q_p`.  Starting from the cyclotomic series
for the uniformizer `p` and a unit `u`, it constructs mutually inverse
series over `W(k)` which conjugate it to the basic Lubin--Tate series for
the uniformizer `p * u`.  The conjugating series satisfies Milne's exact
semilinear equation with Witt Frobenius.
-/

namespace Towers.CField.LTate
open PowerSeries
open Towers.CField.FGroups
noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [CharP k p]

/-- The canonical coefficient embedding `Z_p → W(k)` is injective. -/
theorem int_witt_injective : Function.Injective (padicIntWitt p k) := by
  intro a b h
  apply (WittVector.equiv p).symm.injective
  apply WittVector.map_injective _ (ZMod.castHom (dvd_refl p) k).injective
  exact h
/-- Detect the three Lubin--Tate-series conditions after embedding `Z_p`
into `W(k)` and reducing by the zeroth Witt coefficient. -/
theorem lubin_tate_witt
    (varpi : ℤ_[p])
    (hspan : Ideal.span {varpi} = Ideal.span {(p : ℤ_[p])})
    (g : PowerSeries ℤ_[p])
    (hg0 : constantCoeff (PowerSeries.map (padicIntWitt p k) g) = 0)
    (hg1 : coeff 1 (PowerSeries.map (padicIntWitt p k) g) =
      padicIntWitt p k varpi)
    (hgred : PowerSeries.map WittVector.constantCoeff
      (PowerSeries.map (padicIntWitt p k) g) = X ^ p) :
    LubinSeries varpi p g := by
  let rho := padicIntWitt p k
  let residue : ℤ_[p] →+* k := WittVector.constantCoeff.comp rho
  have hker : RingHom.ker residue = Ideal.span {varpi} := by
    ext a
    rw [RingHom.mem_ker]
    change (rho a).coeff 0 = 0 ↔ a ∈ Ideal.span {varpi}
    rw [coeff_int_witt]
    constructor
    · intro ha
      letI : Fact (Nat.Prime (p ^ 1)) := ⟨by simpa using (Fact.out : p.Prime)⟩
      letI : CharP k (p ^ 1) := by simpa using (inferInstance : CharP k p)
      have hz : PadicInt.toZModPow 1 a = 0 :=
        (ZMod.castHom (dvd_refl (p ^ 1)) k).injective (by simpa using ha)
      rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one] at hz
      rw [hspan]
      exact hz
    · intro ha
      have hz : PadicInt.toZModPow 1 a = 0 := by
        rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, pow_one]
        rw [← hspan]
        exact ha
      rw [hz, map_zero]
  let bar : (ℤ_[p] ⧸ Ideal.span {varpi}) →+* k :=
    Ideal.Quotient.lift _ residue (fun a ha => RingHom.mem_ker.mp (hker.ge ha))
  have hbar : Function.Injective bar := by
    apply RingHom.lift_injective_of_ker_le_ideal
    rw [hker]
  refine ⟨?_, ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map] at hg0
    change rho (coeff 0 g) = 0 at hg0
    exact (int_witt_injective p k) (hg0.trans (map_zero rho).symm)
  · change rho (coeff 1 g) = rho varpi at hg1
    exact (int_witt_injective p k) hg1
  · apply PowerSeries.map_injective bar hbar
    calc
      PowerSeries.map bar
          (PowerSeries.map (Ideal.Quotient.mk (Ideal.span {varpi})) g) =
          PowerSeries.map residue g := by
        apply PowerSeries.ext
        intro n
        simp only [PowerSeries.coeff_map]
        exact Ideal.Quotient.lift_mk _ _ _
      _ = PowerSeries.map WittVector.constantCoeff
          (PowerSeries.map rho g) := by
        apply PowerSeries.ext
        intro n
        rfl
      _ = X ^ p := hgred
      _ = PowerSeries.map bar (X ^ p) := by
        rw [map_pow, PowerSeries.map_X]
end
end Towers.CField.LTate

namespace Towers.CField.LTate
open PowerSeries
open Towers.CField.FGroups
noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]

set_option maxHeartbeats 2000000 in
-- Frobenius descent and the reduction calculation unfold power-series maps.
/-- The unadjusted Step 2 series descends to a Lubin--Tate series over
`Z_p`. -/
theorem uniformizer_change_series (u : ℤ_[p]ˣ) :
    ∃ (g : PowerSeries ℤ_[p]) (epsilon : (WittVector p k)ˣ)
      (theta inverseTheta : PowerSeries (WittVector p k)),
      LubinSeries ((p : ℤ_[p]) * (u : ℤ_[p])) p g ∧
      constantCoeff theta = 0 ∧
      coeff 1 theta = (epsilon : WittVector p k) ∧
      constantCoeff inverseTheta = 0 ∧
      subst inverseTheta theta = X ∧
      subst theta inverseTheta = X ∧
      PowerSeries.map WittVector.frobenius theta =
        subst (PowerSeries.map (padicIntWitt p k)
          (padicBinomialEndomorphism p (u : ℤ_[p]))) theta ∧
      semilinearConjugate WittVector.frobenius theta inverseTheta
          (PowerSeries.map (padicIntWitt p k)
            (cyclotomicPowerSeries (R := ℤ_[p]) p)) =
        PowerSeries.map (padicIntWitt p k) g := by
  let rho := padicIntWitt p k
  let fA := cyclotomicPowerSeries (R := ℤ_[p]) p
  let f := PowerSeries.map rho fA
  let UA := padicBinomialEndomorphism p (u : ℤ_[p])
  let U := PowerSeries.map rho UA
  let uW : (WittVector p k)ˣ := Units.map rho.toMonoidHom u
  obtain ⟨epsilon, hepsilon⟩ := witt_frobenius_eigenunit p k uW
  have hU0 : constantCoeff U = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    simp [UA]
  have hU1 : coeff 1 U = (uW : WittVector p k) := by
    simp [U, UA, uW, rho]
  obtain ⟨theta, htheta0, htheta1, htheta⟩ :=
    SIStep.exists_semilinearTheta
      WittVector.frobenius epsilon uW U hepsilon
      (WittVector.frobenius_sub_surjective p) hU0 hU1
  let inverseTheta := compositionalInverse theta epsilon
  have hinverse0 : constantCoeff inverseTheta = 0 :=
    constant_compositional_inverse theta epsilon
  have hthetaInverse : subst inverseTheta theta = X := by
    exact subst_compositionalInverse epsilon htheta0 htheta1.symm
  have hinverseTheta : subst theta inverseTheta = X :=
    subst_x htheta0 hinverse0 hthetaInverse
  let h := semilinearConjugate WittVector.frobenius theta inverseTheta f
  have hf0 : constantCoeff f = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
    simp [fA, cyclotomicPowerSeries]
  have hfixf : PowerSeries.map WittVector.frobenius f = f := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_map, f, rho]
    exact frobenius_int_witt p k (coeff n fA)
  have hfixU : PowerSeries.map WittVector.frobenius U = U := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_map, U, rho]
    exact frobenius_int_witt p k (coeff n UA)
  have hcommA : subst UA fA = subst fA UA :=
    endomorphism_subst_commute p (u : ℤ_[p])
  have hcomm : subst f U = subst U f := by
    have hUA : PowerSeries.HasSubst UA :=
      PowerSeries.HasSubst.of_constantCoeff_zero'
        (endomorphism_constant_coeff p (u : ℤ_[p]))
    have hfA : PowerSeries.HasSubst fA :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (by
        simp [fA, cyclotomicPowerSeries])
    calc
      subst f U = PowerSeries.map rho (subst fA UA) := by
        exact (PowerSeries.map_subst hfA UA).symm
      _ = PowerSeries.map rho (subst UA fA) := by rw [hcommA]
      _ = subst U f := PowerSeries.map_subst hUA fA
  have hfixh : PowerSeries.map WittVector.frobenius h = h :=
    semilinear_conjugate_self WittVector.frobenius
      hinverse0 hf0 hU0 hthetaInverse htheta hfixf hfixU hcomm
  obtain ⟨g, hgmap⟩ := padic_frobenius_fixed p k h hfixh
  have hh0 : constantCoeff h = 0 :=
    semilinear_constant_coeff WittVector.frobenius htheta0 hinverse0 hf0
  have hf1 : coeff 1 f = rho (p : ℤ_[p]) := by
    simp [f, fA, rho, cyclotomicPowerSeries, PowerSeries.coeff_one_pow]
  have hh1 : coeff 1 h = rho ((p : ℤ_[p]) * (u : ℤ_[p])) := by
    rw [semilinear_conjugate_coeff WittVector.frobenius epsilon uW
      (rho (p : ℤ_[p])) htheta1 hinverse0 hthetaInverse hf0 hf1 hepsilon]
    change rho (p : ℤ_[p]) * rho (u : ℤ_[p]) = rho ((p : ℤ_[p]) * (u : ℤ_[p]))
    rw [map_mul]
  have hcompat :
      (iterateFrobenius k p 1).comp
          (WittVector.constantCoeff : WittVector p k →+* k) =
        (WittVector.constantCoeff : WittVector p k →+* k).comp
          (WittVector.frobenius : WittVector p k →+* WittVector p k) := by
    apply RingHom.ext
    intro x
    simp [iterateFrobenius, WittVector.coeff_frobenius_charP]
  have hfmap : PowerSeries.map WittVector.constantCoeff f = X ^ p := by
    letI : CharP (PowerSeries k) p :=
      charP_of_injective_ringHom (PowerSeries.C_injective (R := k)) p
    simp only [cyclotomicPowerSeries, map_sub, map_pow, map_add, map_one,
      map_X, f, rho, fA]
    rw [add_pow_char]
    simp
  have hhred : PowerSeries.map WittVector.constantCoeff h = X ^ p := by
    simpa only [h, pow_one] using
      (semilinear_x_compatible
        p 1 WittVector.constantCoeff WittVector.frobenius
        hinverse0 hf0 hthetaInverse (by simpa using hfmap) hcompat)
  have hspan : Ideal.span {((p : ℤ_[p]) * (u : ℤ_[p]))} =
      Ideal.span {(p : ℤ_[p])} := by
    exact Ideal.span_singleton_mul_right_unit u.isUnit (p : ℤ_[p])
  have hg0 : constantCoeff (PowerSeries.map rho g) = 0 := by rw [hgmap, hh0]
  have hg1 : coeff 1 (PowerSeries.map rho g) =
      rho ((p : ℤ_[p]) * (u : ℤ_[p])) := by rw [hgmap, hh1]
  have hgred : PowerSeries.map WittVector.constantCoeff
      (PowerSeries.map rho g) = X ^ p := by rw [hgmap, hhred]
  have hg : LubinSeries ((p : ℤ_[p]) * (u : ℤ_[p])) p g :=
    lubin_tate_witt p k _ hspan g hg0 hg1 hgred
  exact ⟨g, epsilon, theta, inverseTheta, hg, htheta0, htheta1,
    hinverse0, hthetaInverse, hinverseTheta, htheta, hgmap.symm⟩

end
end Towers.CField.LTate

namespace Towers.CField.LTate
open PowerSeries
open Towers.CField.FGroups
noncomputable section

variable (p : ℕ) [Fact p.Prime]
variable (k : Type*) [Field k] [CharP k p] [IsAlgClosed k]

set_option maxHeartbeats 3000000 in
-- The final canonical adjustment unfolds both scalar intertwiners.
/-- Proposition I.3.10 for the cyclotomic series and the basic series
`(p*u)X + X^p`, including the inverse series and semilinear equation. -/
theorem witt_uniformizer_change (u : ℤ_[p]ˣ) :
    let varpi : ℤ_[p] := (p : ℤ_[p]) * (u : ℤ_[p])
    let g : PowerSeries ℤ_[p] :=
      (basicLubinTate varpi p : Polynomial ℤ_[p])
    ∃ (epsilon : (WittVector p k)ˣ)
      (theta inverseTheta : PowerSeries (WittVector p k)),
      constantCoeff theta = 0 ∧
      coeff 1 theta = (epsilon : WittVector p k) ∧
      constantCoeff inverseTheta = 0 ∧
      subst inverseTheta theta = X ∧
      subst theta inverseTheta = X ∧
      PowerSeries.map WittVector.frobenius theta =
        subst (PowerSeries.map (padicIntWitt p k)
          (padicBinomialEndomorphism p (u : ℤ_[p]))) theta ∧
      semilinearConjugate WittVector.frobenius theta inverseTheta
          (PowerSeries.map (padicIntWitt p k)
            (cyclotomicPowerSeries (R := ℤ_[p]) p)) =
        PowerSeries.map (padicIntWitt p k) g := by
  dsimp only
  let rho := padicIntWitt p k
  let varpi : ℤ_[p] := (p : ℤ_[p]) * (u : ℤ_[p])
  let gBasic : PowerSeries ℤ_[p] :=
    (basicLubinTate varpi p : Polynomial ℤ_[p])
  obtain ⟨hA, epsilon, theta, inverseTheta, hhA, htheta0,
      htheta1, hinverse0, hthetaInverse, hinverseTheta,
      hsemilinear, hconjugate⟩ :=
    uniformizer_change_series p k u
  have hvarpi0 : varpi ≠ 0 := mul_ne_zero (padic_int_ne p) u.ne_zero
  have hvarpi : ¬ IsUnit varpi := by
    intro h
    exact padic_int_unit p ((IsUnit.mul_iff.mp h).1)
  have hspan : Ideal.span {varpi} = Ideal.span {(p : ℤ_[p])} := by
    exact Ideal.span_singleton_mul_right_unit u.isUnit (p : ℤ_[p])
  letI : Fintype (ℤ_[p] ⧸ Ideal.span {varpi}) :=
    Fintype.ofEquiv (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])})
      (Ideal.quotEquivOfEq hspan).symm.toEquiv
  have hfield : IsField (ℤ_[p] ⧸ Ideal.span {varpi}) := by
    rw [hspan]
    exact padic_int_field p
  have hcard : Fintype.card (ℤ_[p] ⧸ Ideal.span {varpi}) = p := by
    rw [Fintype.card_congr (Ideal.quotEquivOfEq hspan).toEquiv]
    exact padic_int_card p
  have hhA' : LubinSeries varpi
      (Fintype.card (ℤ_[p] ⧸ Ideal.span {varpi})) hA := by
    rwa [hcard]
  have hgBasic : LubinSeries varpi
      (Fintype.card (ℤ_[p] ⧸ Ideal.span {varpi})) gBasic := by
    rw [hcard]
    exact lubin_tate_basic varpi (Fact.out : p.Prime).one_lt
  let iA := lubinScalarIntertwiner varpi hvarpi0 hvarpi
    hfield hA gBasic hhA' hgBasic 1
  let jA := lubinScalarIntertwiner varpi hvarpi0 hvarpi
    hfield gBasic hA hgBasic hhA' 1
  let iW := PowerSeries.map rho iA
  let jW := PowerSeries.map rho jA
  let theta' := subst theta iW
  let inverseTheta' := subst jW inverseTheta
  have hiA0 : constantCoeff iA = 0 :=
    lubin_intertwiner_coeff
      varpi hvarpi0 hvarpi hfield hA gBasic hhA' hgBasic 1
  have hjA0 : constantCoeff jA = 0 :=
    lubin_intertwiner_coeff
      varpi hvarpi0 hvarpi hfield gBasic hA hgBasic hhA' 1
  have hiW0 : constantCoeff iW = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, hiA0, map_zero]
  have hjW0 : constantCoeff jW = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, hjA0, map_zero]
  have hfixi : PowerSeries.map WittVector.frobenius iW = iW := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_map, iW, rho]
    exact frobenius_int_witt p k (coeff n iA)
  have hfixj : PowerSeries.map WittVector.frobenius jW = jW := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_map, jW, rho]
    exact frobenius_int_witt p k (coeff n jA)
  have hijA : subst jA iA = X :=
    lubin_intertwiner_inverse
      varpi hvarpi0 hvarpi hfield hA gBasic hhA' hgBasic
  have hjiA : subst iA jA = X :=
    lubin_intertwiner_inverse
      varpi hvarpi0 hvarpi hfield gBasic hA hgBasic hhA'
  have hijW : subst jW iW = X := by
    have hjSubst : PowerSeries.HasSubst jA :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hjA0
    calc
      subst jW iW = PowerSeries.map rho (subst jA iA) := by
        exact (PowerSeries.map_subst hjSubst iA).symm
      _ = X := by rw [hijA, PowerSeries.map_X]
  have hjiW : subst iW jW = X := by
    have hiSubst : PowerSeries.HasSubst iA :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hiA0
    calc
      subst iW jW = PowerSeries.map rho (subst iA jA) := by
        exact (PowerSeries.map_subst hiSubst jA).symm
      _ = X := by rw [hjiA, PowerSeries.map_X]
  have hintertwinesA : subst iA gBasic = subst hA iA :=
    lubin_intertwiner_intertwines
      varpi hvarpi0 hvarpi hfield hA gBasic hhA' hgBasic 1
  have hintertwinesW :
      subst iW (PowerSeries.map rho gBasic) =
        subst (PowerSeries.map rho hA) iW := by
    have hiSubst : PowerSeries.HasSubst iA :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hiA0
    have hhA0 : constantCoeff hA = 0 := by
      simpa only [← coeff_zero_eq_constantCoeff_apply] using hhA'.1
    have hhASubst : PowerSeries.HasSubst hA :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hhA0
    calc
      subst iW (PowerSeries.map rho gBasic) =
          PowerSeries.map rho (subst iA gBasic) := by
        exact (PowerSeries.map_subst hiSubst gBasic).symm
      _ = PowerSeries.map rho (subst hA iA) := by rw [hintertwinesA]
      _ = subst (PowerSeries.map rho hA) iW :=
        PowerSeries.map_subst (h := rho) hhASubst iA
  have htheta'0 : constantCoeff theta' = 0 :=
    constantCoeff_subst_eq_zero htheta0 iW hiW0
  have hinverseTheta'0 : constantCoeff inverseTheta' = 0 :=
    constantCoeff_subst_eq_zero hjW0 inverseTheta hinverse0
  have htheta'Inverse : subst inverseTheta' theta' = X :=
    subst_adjusted_theta
      htheta0 hinverse0 hjW0 hthetaInverse hijW
  have hinverseTheta' : subst theta' inverseTheta' = X := by
    exact subst_x htheta'0 hinverseTheta'0 htheta'Inverse
  have htheta'Semilinear :
      PowerSeries.map WittVector.frobenius theta' =
        subst (PowerSeries.map rho
          (padicBinomialEndomorphism p (u : ℤ_[p]))) theta' := by
    exact subst_semilinear_fixed
      WittVector.frobenius htheta0
      (by
        rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
        simp)
      hsemilinear hfixi
  have htheta'Conjugate :
      semilinearConjugate WittVector.frobenius theta' inverseTheta'
          (PowerSeries.map rho
            (cyclotomicPowerSeries (R := ℤ_[p]) p)) =
        PowerSeries.map rho gBasic := by
    apply semilinear_subst_intertwines
      WittVector.frobenius hiW0 hjW0 htheta0 hinverse0
    · rw [← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
      simp [cyclotomicPowerSeries]
    · exact hfixi
    · exact hijW
    · rw [hconjugate]
      exact hintertwinesW
  have hiA1 : coeff 1 iA = 1 :=
    lubin_tate_intertwiner
      varpi hvarpi0 hvarpi hfield hA gBasic hhA' hgBasic 1
  have htheta'1 : coeff 1 theta' = (epsilon : WittVector p k) := by
    change coeff 1 (subst theta iW) = (epsilon : WittVector p k)
    rw [one_subst htheta0 (by
      change coeff 1 (PowerSeries.map rho iA) = 1
      rw [PowerSeries.coeff_map, hiA1, map_one])]
    exact htheta1
  exact ⟨epsilon, theta', inverseTheta', htheta'0, htheta'1,
    hinverseTheta'0, htheta'Inverse, hinverseTheta', htheta'Semilinear,
    htheta'Conjugate⟩

end
end Towers.CField.LTate

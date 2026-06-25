import Towers.ClassField.FormalGroups.PAdicIntegers
import Towers.ClassField.LubinTate.RootField

/-!
# The cyclotomic Lubin--Tate datum over `Z_p`

This file specializes the polynomial finite-level Lubin--Tate construction to
Milne's cyclotomic series `(1 + X)^p - 1` over `Z_p`.  It is the algebraic
starting point for identifying the abstract Lubin--Tate root field with
`Q_p(zeta_(p^r))` in Examples I.3.8 and I.3.13.
-/

namespace Towers.CField.LTate

open Polynomial
open Towers.CField.FGroups

noncomputable section

/-- The valuation-integer presentation used by the generic local-field
Lubin--Tate theorems is the usual subtype presentation of `Z_p`. -/
theorem padic_int_subring
    (p : ℕ) [Fact p.Prime] :
    Valuation.integer (NormedField.valuation (K := ℚ_[p])) =
      PadicInt.subring p := by
  ext x
  simp only [PadicInt.subring, Valuation.mem_integer_iff,
    NormedField.valuation_apply, Subring.mem_mk]
  constructor <;> intro h <;> exact_mod_cast h

/-- Forgetting the explicit `Subring` wrapper recovers Mathlib's `PadicInt`
type. -/
noncomputable def padicIntSubring
    (p : ℕ) [Fact p.Prime] : (PadicInt.subring p) ≃+* ℤ_[p] where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Canonical identity-on-elements equivalence between the two integer-ring
presentations used by the local-field and p-adic APIs. -/
noncomputable def padicNormInt
    (p : ℕ) [Fact p.Prime] :
    Valuation.integer (NormedField.valuation (K := ℚ_[p])) ≃+* ℤ_[p] :=
  (RingEquiv.subringCongr (padic_int_subring p)).trans
    (padicIntSubring p)

noncomputable instance discreteValuationRing
    (p : ℕ) [Fact p.Prime] :
    IsDiscreteValuationRing
      (Valuation.integer (NormedField.valuation (K := ℚ_[p]))) := by
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (padicNormInt p).symm

/-- Milne's cyclotomic Lubin--Tate polynomial, now with coefficients in
`Z_p`. -/
def padicCyclotomicLubin
    (p : ℕ) [Fact p.Prime] : ℤ_[p][X] :=
  (1 + X) ^ p - 1

@[simp]
theorem padic_cyclotomic_lubin
    (p : ℕ) [Fact p.Prime] :
    (padicCyclotomicLubin p).coeff 0 = 0 := by
  rw [padicCyclotomicLubin, coeff_sub,
    coeff_one_add_X_pow, coeff_one]
  simp

@[simp]
theorem padic_lubin_coeff
    (p : ℕ) [Fact p.Prime] :
    (padicCyclotomicLubin p).coeff 1 = p := by
  rw [padicCyclotomicLubin, coeff_sub,
    coeff_one_add_X_pow, coeff_one]
  simp

/-- The cyclotomic polynomial is monic of degree `p`. -/
theorem padic_lubin_monic
    (p : ℕ) [Fact p.Prime] :
    (padicCyclotomicLubin p).Monic := by
  have hmonic : ((1 + X : ℤ_[p][X]) ^ p).Monic := by
    exact (by simpa [add_comm] using
      ((monic_X_add_C (1 : ℤ_[p])).pow p))
  have hdegree : degree (1 : ℤ_[p][X]) <
      degree ((1 + X : ℤ_[p][X]) ^ p) := by
    rw [degree_one, degree_eq_natDegree hmonic.ne_zero]
    have hnat : ((1 + X : ℤ_[p][X]) ^ p).natDegree = p := by
      simpa [add_comm] using
        (natDegree_pow_X_add_C p (1 : ℤ_[p]))
    rw [hnat]
    exact_mod_cast (Fact.out : p.Prime).pos
  rw [padicCyclotomicLubin]
  exact hmonic.sub_of_left hdegree

@[simp]
theorem padic_lubin_degree
    (p : ℕ) [Fact p.Prime] :
    (padicCyclotomicLubin p).natDegree = p := by
  rw [padicCyclotomicLubin,
    show (1 : ℤ_[p][X]) = C 1 by rfl, natDegree_sub_C]
  simpa [add_comm] using
    (natDegree_pow_X_add_C p (1 : ℤ_[p]))

/-- The concrete polynomial datum whose level `r` root field is the
cyclotomic Lubin--Tate extension of conductor `p^(r+1)`. -/
noncomputable def cyclotomicLubinDatum
    (p : ℕ) [Fact p.Prime] : LTDatum ℤ_[p] where
  pi := p
  q := p
  residueCard := by
    rw [Nat.card_eq_fintype_card]
    exact padic_int_card p
  f := padicCyclotomicLubin p
  pi_irreducible := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    exact PadicInt.maximalIdeal_eq_span_p
  f_monic := padic_lubin_monic p
  f_natDegree := padic_lubin_degree p
  one_lt_q := (Fact.out : p.Prime).one_lt
  lubinTateSeries := by
    simpa [padicCyclotomicLubin, cyclotomicPowerSeries,
      padic_int_card] using
        (lubin_tate_cyclotomic p)

/-- The cyclotomic datum transported to the valuation-integer presentation
used by the generic spectral root-field theorems. -/
noncomputable def padicLubinDatum
    (p : ℕ) [Fact p.Prime] :
    LTDatum
      (Valuation.integer (NormedField.valuation (K := ℚ_[p]))) := by
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let e : A ≃+* ℤ_[p] := padicNormInt p
  let D := cyclotomicLubinDatum p
  let pi : A := e.symm D.pi
  let f : A[X] := D.f.map e.symm.toRingHom
  let I : Ideal A := Ideal.span {pi}
  let J : Ideal ℤ_[p] := Ideal.span {D.pi}
  have hIJ : J = I.map e.toRingHom := by
    change Ideal.span {D.pi} = (Ideal.span {pi}).map e.toRingHom
    rw [Ideal.map_span]
    congr 1
    simp [pi]
  let eQ : (A ⧸ I) ≃+* (ℤ_[p] ⧸ J) :=
    Ideal.quotientEquiv I J e hIJ
  refine
    { pi := pi
      q := D.q
      residueCard := ?_
      f := f
      pi_irreducible := ?_
      f_monic := ?_
      f_natDegree := ?_
      one_lt_q := D.one_lt_q
      lubinTateSeries := ?_ }
  · calc
      Nat.card (A ⧸ Ideal.span {pi}) = Nat.card (A ⧸ I) := rfl
      _ = Nat.card (ℤ_[p] ⧸ J) := Nat.card_congr eQ.toEquiv
      _ = Nat.card (ℤ_[p] ⧸ Ideal.span {D.pi}) := rfl
      _ = D.q := D.residueCard
  · exact D.pi_irreducible.map e.symm.toMulEquiv
  · exact D.f_monic.map e.symm.toRingHom
  · exact (D.f_monic.natDegree_map e.symm.toRingHom).trans D.f_natDegree
  · constructor
    · change PowerSeries.coeff 0 (f : PowerSeries A) = 0
      simp [f, D.lubinTateSeries.1]
    constructor
    · change PowerSeries.coeff 1 (f : PowerSeries A) = pi
      simp [f, pi, D.lubinTateSeries.2.1]
    · change PowerSeries.map (Ideal.Quotient.mk I) (f : PowerSeries A) =
        PowerSeries.X ^ D.q
      apply PowerSeries.map_injective eQ.toRingHom eQ.injective
      have hcomp : eQ.toRingHom.comp (Ideal.Quotient.mk I) =
          (Ideal.Quotient.mk J).comp e.toRingHom := by
        ext a
        rfl
      simp only [map_pow, PowerSeries.map_X]
      have hmap : PowerSeries.map e.toRingHom (f : PowerSeries A) =
          (D.f : PowerSeries ℤ_[p]) := by
        rw [← Polynomial.polynomial_map_coe]
        rw [Polynomial.coe_inj]
        ext n
        simp [f]
      calc
        PowerSeries.map eQ.toRingHom
            (PowerSeries.map (Ideal.Quotient.mk I) (f : PowerSeries A)) =
            PowerSeries.map
              (eQ.toRingHom.comp (Ideal.Quotient.mk I))
              (f : PowerSeries A) := by
          rfl
        _ = PowerSeries.map
              ((Ideal.Quotient.mk J).comp e.toRingHom)
              (f : PowerSeries A) := by rw [hcomp]
        _ = PowerSeries.map (Ideal.Quotient.mk J)
              (PowerSeries.map e.toRingHom (f : PowerSeries A)) := by
          rfl
        _ = PowerSeries.map (Ideal.Quotient.mk J)
              (D.f : PowerSeries ℤ_[p]) := by rw [hmap]
        _ = PowerSeries.X ^ D.q := D.lubinTateSeries.2.2

/-- Reduction from `Z_p` onto `Z/p^r Z`, kept in Chapter I so the
Lubin--Tate quotient coordinates do not depend on the later Example VII.8.2
wrapper. -/
theorem z_mod_surjective
    (p r : ℕ) [Fact p.Prime] :
    Function.Surjective (PadicInt.toZModPow (p := p) r) := by
  intro x
  refine ⟨((x.val : ℕ) : ℤ_[p]), ?_⟩
  calc
    PadicInt.toZModPow r ((x.val : ℕ) : ℤ_[p]) =
        ((x.val : ℕ) : ZMod (p ^ r)) := map_natCast _ _
    _ = x := by simp

/-- The quotient ring used by the finite Lubin--Tate action is canonically
`Z/p^r Z`. -/
noncomputable def intZMod
    (p r : ℕ) [Fact p.Prime] :
    (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ r}) ≃+* ZMod (p ^ r) :=
  (Ideal.quotEquivOfEq (PadicInt.ker_toZModPow r).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (z_mod_surjective p r))

@[simp]
theorem z_mod_mk
    (p r : ℕ) [Fact p.Prime] (a : ℤ_[p]) :
    intZMod p r
        (Ideal.Quotient.mk (Ideal.span {(p : ℤ_[p]) ^ r}) a) =
      PadicInt.toZModPow r a := by
  simp [intZMod]

/-- Unit-group form of the finite Lubin--Tate quotient coordinate. -/
noncomputable def unitsZMod
    (p r : ℕ) [Fact p.Prime] :
    (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ r})ˣ ≃* (ZMod (p ^ r))ˣ :=
  Units.mapEquiv (intZMod p r).toMulEquiv

/-- Quotient-ring coordinate change from the valuation-integer presentation
to the usual `Z_p` presentation. -/
noncomputable def padicIntegerInt
    (p r : ℕ) [Fact p.Prime] :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    (A ⧸ Ideal.span {D.pi ^ r}) ≃+*
      (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ r}) := by
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let e : A ≃+* ℤ_[p] := padicNormInt p
  let D := padicLubinDatum p
  let I : Ideal A := Ideal.span {D.pi ^ r}
  let J : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p]) ^ r}
  have hIJ : J = I.map e.toRingHom := by
    change Ideal.span {(p : ℤ_[p]) ^ r} =
      (Ideal.span {(e.symm (p : ℤ_[p])) ^ r}).map e.toRingHom
    rw [Ideal.map_span]
    congr 1
    simp
  exact Ideal.quotientEquiv I J e hIJ

/-- Composite finite coordinate from the valuation-integer quotient directly
to `Z/p^r Z`. -/
noncomputable def integerZMod
    (p r : ℕ) [Fact p.Prime] :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    (A ⧸ Ideal.span {D.pi ^ r}) ≃+* ZMod (p ^ r) :=
  (padicIntegerInt p r).trans
    (intZMod p r)

@[simp]
theorem padic_z_mk
    (p r : ℕ) [Fact p.Prime]
    (a : Valuation.integer (NormedField.valuation (K := ℚ_[p]))) :
    integerZMod p r
        (Ideal.Quotient.mk
          (Ideal.span {(padicLubinDatum p).pi ^ r}) a) =
      PadicInt.toZModPow r (padicNormInt p a) := by
  simp [integerZMod,
    padicIntegerInt]

/-- The finite quotient units for the valuation-integer datum have the
standard cyclotomic coordinate `(ZMod (p^r))ˣ`. -/
noncomputable def padicZMod
    (p r : ℕ) [Fact p.Prime] :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    (A ⧸ Ideal.span {D.pi ^ r})ˣ ≃* (ZMod (p ^ r))ˣ :=
  Units.mapEquiv (integerZMod p r).toMulEquiv

/-- The least natural representative of the standard `ZMod` coordinate is a
lift of the original quotient unit. -/
theorem padic_integer_lift
    (p r : ℕ) [Fact p.Prime]
    (u : let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
      let D := padicLubinDatum p
      (A ⧸ Ideal.span {D.pi ^ r})ˣ) :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    Ideal.Quotient.mk (Ideal.span {D.pi ^ r})
        (((padicZMod p r u :
          ZMod (p ^ r)).val : ℕ) : A) =
      (u : A ⧸ Ideal.span {D.pi ^ r}) := by
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let D := padicLubinDatum p
  let eR := integerZMod p r
  let eU := padicZMod p r
  apply eR.injective
  rw [padic_z_mk]
  simp only [map_natCast]
  change (((eU u : ZMod (p ^ r)).val : ℕ) : ZMod (p ^ r)) =
    eR (u : A ⧸ Ideal.span {D.pi ^ r})
  have hcoe : (eU u : ZMod (p ^ r)) =
      eR (u : A ⧸ Ideal.span {D.pi ^ r}) := rfl
  rw [← hcoe]
  exact ZMod.natCast_zmod_val _

/-- Reduce a conventional `Z_p` unit into the finite quotient attached to
the valuation-integer presentation of the Lubin--Tate datum. -/
noncomputable def padicIntInteger
    (p r : ℕ) [Fact p.Prime] :
    ℤ_[p]ˣ →*
      let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
      let D := padicLubinDatum p
      (A ⧸ Ideal.span {D.pi ^ r})ˣ :=
  (Units.map
      (Ideal.Quotient.mk
        (Ideal.span {(padicLubinDatum p).pi ^ r})).toMonoidHom).comp
    (Units.mapEquiv
      (padicNormInt p).symm.toMulEquiv).toMonoidHom

/-- The transported quotient reduction has the standard `ZMod` coordinate. -/
theorem padic_z_reduction
    (p r : ℕ) [Fact p.Prime] (u : ℤ_[p]ˣ) :
    padicZMod p r
        (padicIntInteger p r u) =
      Units.map (PadicInt.toZModPow (p := p) r).toMonoidHom u := by
  apply Units.ext
  change integerZMod p r
      (Ideal.Quotient.mk
        (Ideal.span {(padicLubinDatum p).pi ^ r})
        ((padicNormInt p).symm (u : ℤ_[p]))) =
    PadicInt.toZModPow r (u : ℤ_[p])
  rw [padic_z_mk]
  simp

/-- Residue-field coordinate change for the transported datum.  This
separate level-one form avoids casts between quotient types whose ideals are
only propositionally equal after simplifying `x ^ 1`. -/
noncomputable def integerResidueInt
    (p : ℕ) [Fact p.Prime] :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    (A ⧸ Ideal.span {D.pi}) ≃+*
      (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let e : A ≃+* ℤ_[p] := padicNormInt p
  let D := padicLubinDatum p
  let I : Ideal A := Ideal.span {D.pi}
  let J : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p])}
  have hIJ : J = I.map e.toRingHom := by
    change Ideal.span {(p : ℤ_[p])} =
      (Ideal.span {e.symm (p : ℤ_[p])}).map e.toRingHom
    rw [Ideal.map_span]
    congr 1
    simp
  exact Ideal.quotientEquiv I J e hIJ

/-- The residue quotient of the transported datum is a field. -/
theorem padic_integer_residue
    (p : ℕ) [Fact p.Prime] :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := padicLubinDatum p
    IsField (A ⧸ Ideal.span {D.pi}) := by
  exact (integerResidueInt p).toMulEquiv.isField
    (padic_int_field p)

/-- In the valuation-integer presentation, the transported polynomial is
still the literal cyclotomic series `(1 + X)^p - 1`. -/
theorem lubin_datum_f
    (p : ℕ) [Fact p.Prime] :
    ((padicLubinDatum p).f :
        PowerSeries
          (Valuation.integer (NormedField.valuation (K := ℚ_[p])))) =
      cyclotomicPowerSeries
        (R := Valuation.integer (NormedField.valuation (K := ℚ_[p]))) p := by
  change
    ((padicCyclotomicLubin p).map
        (padicNormInt p).symm.toRingHom :
      PowerSeries
        (Valuation.integer (NormedField.valuation (K := ℚ_[p])))) = _
  rw [Polynomial.polynomial_map_coe]
  simp [padicCyclotomicLubin, cyclotomicPowerSeries]

/-- Iterating `(1 + X)^p - 1` is the same as raising `1 + X` to the
corresponding `p`-power. -/
theorem padic_lubin_iterate
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ((padicCyclotomicLubin p).comp^[n]) X =
      (1 + X : ℤ_[p][X]) ^ (p ^ n) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [padicCyclotomicLubin, sub_comp, pow_comp,
        add_comp, one_comp, X_comp]
      rw [show (1 : ℤ_[p][X]) + ((1 + X) ^ p ^ n - 1) =
          (1 + X) ^ p ^ n by ring]
      rw [← pow_mul, pow_succ]

/-- Dividing the cyclotomic Lubin--Tate polynomial by `X` gives the expected
geometric sum. -/
theorem lubin_div_x
    (p : ℕ) [Fact p.Prime] :
    (padicCyclotomicLubin p).divX =
      ∑ i ∈ Finset.range p, (1 + X : ℤ_[p][X]) ^ i := by
  apply mul_left_cancel₀ (X_ne_zero : (X : ℤ_[p][X]) ≠ 0)
  have hdiv := X_mul_divX_add (padicCyclotomicLubin p)
  rw [padic_cyclotomic_lubin, C_0, add_zero] at hdiv
  rw [hdiv]
  have hgeom := geom_sum_mul_add (X : ℤ_[p][X]) p
  rw [add_comm X 1] at hgeom
  calc
    padicCyclotomicLubin p =
        (1 + X : ℤ_[p][X]) ^ p - 1 := rfl
    _ = (∑ i ∈ Finset.range p, (1 + X : ℤ_[p][X]) ^ i) * X := by
      exact sub_eq_iff_eq_add.mpr hgeom.symm
    _ = X * ∑ i ∈ Finset.range p, (1 + X : ℤ_[p][X]) ^ i := by
      rw [mul_comm]

/-- Milne's reduced level-`n+1` Lubin--Tate polynomial is the shifted
`p^(n+1)`-st cyclotomic polynomial. -/
theorem reduced_iterate_shifted
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    reducedLubinIterate (padicCyclotomicLubin p) n =
      (cyclotomic (p ^ (n + 1)) ℤ_[p]).comp (X + 1) := by
  rw [reducedLubinIterate,
    lubin_div_x,
    padic_lubin_iterate,
    cyclotomic_prime_pow_eq_geom_sum (Fact.out : p.Prime)]
  simp only [Polynomial.sum_comp, pow_comp, add_comp, one_comp, X_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (1 : ℤ_[p][X]) + ((1 + X) ^ p ^ n - 1) =
      (1 + X) ^ p ^ n by ring]
  congr 2
  rw [add_comm X 1]

/-- After extending coefficients to `Q_p`, the concrete reduced polynomial
is still the shifted cyclotomic polynomial. -/
theorem tate_datum_reduced
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (cyclotomicLubinDatum p).reducedPolynomial ℚ_[p] n =
      (cyclotomic (p ^ (n + 1)) ℚ_[p]).comp (X + 1) := by
  change
    (reducedLubinIterate
      (padicCyclotomicLubin p) n).map
        (algebraMap ℤ_[p] ℚ_[p]) = _
  rw [reduced_iterate_shifted]
  rw [Polynomial.map_comp, map_cyclotomic]
  simp

/-- The prime-power cyclotomic polynomial is irreducible over `Q_p`.  This is
the translated form of the Eisenstein irreducibility already built into the
Lubin--Tate root-field construction. -/
theorem padicCyclotomic_irreducible
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    Irreducible (cyclotomic (p ^ (n + 1)) ℚ_[p]) := by
  let D := cyclotomicLubinDatum p
  have hshift : Irreducible
      ((cyclotomic (p ^ (n + 1)) ℚ_[p]).comp (X + 1)) := by
    rw [← tate_datum_reduced p n]
    exact D.reducedPolynomial_irreducible ℚ_[p] n
  have heq : Polynomial.algEquivAevalXAddC (1 : ℚ_[p])
      (cyclotomic (p ^ (n + 1)) ℚ_[p]) =
        (cyclotomic (p ^ (n + 1)) ℚ_[p]).comp (X + 1) := by
    exact (Polynomial.comp_eq_aeval (R := ℚ_[p])).symm
  rw [← heq] at hshift
  exact (MulEquiv.irreducible_iff
    (Polynomial.algEquivAevalXAddC (1 : ℚ_[p])).toMulEquiv).mp hshift

/-- Transporting the cyclotomic datum from `Z_p` to the valuation-integer
presentation does not change its reduced polynomial after extending
coefficients to `Q_p`. -/
theorem lubin_datum_reduced
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicLubinDatum p).reducedPolynomial ℚ_[p] n =
      (cyclotomicLubinDatum p).reducedPolynomial ℚ_[p] n := by
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let e : A ≃+* ℤ_[p] := padicNormInt p
  let D := cyclotomicLubinDatum p
  have hcoeff : algebraMap A ℚ_[p] =
      (algebraMap ℤ_[p] ℚ_[p]).comp e.toRingHom := by
    ext a
    rfl
  change
    (reducedLubinIterate (D.f.map e.symm.toRingHom) n).map
        (algebraMap A ℚ_[p]) =
      (reducedLubinIterate D.f n).map (algebraMap ℤ_[p] ℚ_[p])
  rw [hcoeff, ← Polynomial.map_map, lubin_tate_iterate]
  congr 2
  ext i
  simp

/-- The abstract root fields attached to the two presentations of the
cyclotomic datum are canonically equivalent. -/
noncomputable def padicIntegerAlg
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    (padicLubinDatum p).RootField ℚ_[p] n ≃ₐ[ℚ_[p]]
      (cyclotomicLubinDatum p).RootField ℚ_[p] n :=
  AdjoinRoot.algEquivOfEq ℚ_[p]
    ((padicLubinDatum p).reducedPolynomial ℚ_[p] n)
    ((cyclotomicLubinDatum p).reducedPolynomial ℚ_[p] n)
    (lubin_datum_reduced p n)

@[simp]
theorem padic_integer_alg
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicIntegerAlg p n
        ((padicLubinDatum p).root ℚ_[p] n) =
      (cyclotomicLubinDatum p).root ℚ_[p] n := by
  exact AdjoinRoot.algEquivOfEq_root _ _ _

/-- A specified primitive `p^(n+1)`-st root has translate `ζ - 1` as a
root of the concrete Lubin--Tate level polynomial.  Unlike the later
cyclotomic-extension wrapper, this theorem retains the caller's chosen
primitive root. -/
theorem padic_primitive_reduced
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    (ζ : E) (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) :
    IsRoot
      (((cyclotomicLubinDatum p).reducedPolynomial ℚ_[p] n).map
        (algebraMap ℚ_[p] E))
      (ζ - 1) := by
  letI : CharZero E :=
    (RingHom.charZero_iff (algebraMap ℚ_[p] E).injective).mp inferInstance
  letI : NeZero (p ^ (n + 1) : E) :=
    ⟨pow_ne_zero _
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)⟩
  rw [tate_datum_reduced]
  rw [Polynomial.map_comp, map_cyclotomic]
  have hmap : (X + 1 : ℚ_[p][X]).map (algebraMap ℚ_[p] E) =
      (X + 1 : E[X]) := by simp
  rw [hmap]
  rw [IsRoot.def, eval_comp]
  rw [show (X + 1).eval (ζ - 1) = ζ by simp]
  exact hζ.isRoot_cyclotomic
    (pow_pos (Fact.out : p.Prime).pos (n + 1))

/-- The root-field homomorphism associated to a caller-specified primitive
root, sending the distinguished Lubin--Tate root to `ζ - 1`. -/
noncomputable def padicPrimitiveAlg
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    (ζ : E) (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) :
    (cyclotomicLubinDatum p).RootField ℚ_[p] n →ₐ[ℚ_[p]] E :=
  AdjoinRoot.liftAlgHom
    ((cyclotomicLubinDatum p).reducedPolynomial ℚ_[p] n)
    (Algebra.ofId ℚ_[p] E) (ζ - 1)
    (by
      simpa [Polynomial.aeval_def] using
        (padic_primitive_reduced
          p n E ζ hζ))

@[simp]
theorem padic_primitive_alg
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    (ζ : E) (hζ : IsPrimitiveRoot ζ (p ^ (n + 1))) :
    padicPrimitiveAlg p n E ζ hζ
        ((cyclotomicLubinDatum p).root ℚ_[p] n) = ζ - 1 := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- If the specified translated root generates the target, the associated
root-field homomorphism is surjective. -/
theorem padic_primitive_surjective
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    (ζ : E) (hζ : IsPrimitiveRoot ζ (p ^ (n + 1)))
    (hadjoin : Algebra.adjoin ℚ_[p] ({ζ - 1} : Set E) = ⊤) :
    Function.Surjective
      (padicPrimitiveAlg p n E ζ hζ) := by
  rw [← AlgHom.range_eq_top]
  apply top_unique
  rw [← hadjoin]
  apply Algebra.adjoin_le
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  refine ⟨(cyclotomicLubinDatum p).root ℚ_[p] n, ?_⟩
  exact padic_primitive_alg p n E ζ hζ

/-- The abstract cyclotomic Lubin--Tate root field identified with a target
using a specified primitive root. -/
noncomputable def padicAlgPrimitive
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    (ζ : E) (hζ : IsPrimitiveRoot ζ (p ^ (n + 1)))
    (hadjoin : Algebra.adjoin ℚ_[p] ({ζ - 1} : Set E) = ⊤) :
    (cyclotomicLubinDatum p).RootField ℚ_[p] n ≃ₐ[ℚ_[p]] E :=
  AlgEquiv.ofBijective
    (padicPrimitiveAlg p n E ζ hζ)
    ⟨(padicPrimitiveAlg p n E ζ hζ).injective,
      padic_primitive_surjective
        p n E ζ hζ hadjoin⟩

@[simp]
theorem padic_alg_primitive
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    (ζ : E) (hζ : IsPrimitiveRoot ζ (p ^ (n + 1)))
    (hadjoin : Algebra.adjoin ℚ_[p] ({ζ - 1} : Set E) = ⊤) :
    padicAlgPrimitive p n E ζ hζ hadjoin
        ((cyclotomicLubinDatum p).root ℚ_[p] n) = ζ - 1 :=
  padic_primitive_alg p n E ζ hζ

/-- In a `p^(n+1)`-cyclotomic extension of `Q_p`, the translated primitive
root `zeta - 1` is a root of the concrete Lubin--Tate level polynomial. -/
theorem padic_zeta_reduced
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E] :
    IsRoot
      (((cyclotomicLubinDatum p).reducedPolynomial ℚ_[p] n).map
        (algebraMap ℚ_[p] E))
      (IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E - 1) := by
  letI : CharZero E :=
    (RingHom.charZero_iff (algebraMap ℚ_[p] E).injective).mp inferInstance
  letI : NeZero (p ^ (n + 1) : E) :=
    ⟨pow_ne_zero _
      (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)⟩
  rw [tate_datum_reduced]
  rw [Polynomial.map_comp, map_cyclotomic]
  have hmap : (X + 1 : ℚ_[p][X]).map (algebraMap ℚ_[p] E) =
      (X + 1 : E[X]) := by simp
  rw [hmap]
  rw [IsRoot.def, eval_comp]
  rw [show (X + 1).eval
      (IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E - 1) =
        IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E by simp]
  exact IsCyclotomicExtension.zeta_isRoot (p ^ (n + 1)) ℚ_[p] E

/-- The canonical homomorphism from the abstract Lubin--Tate root field to a
cyclotomic extension, sending the distinguished root to `zeta - 1`. -/
noncomputable def padicAlgHom
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E] :
    (cyclotomicLubinDatum p).RootField ℚ_[p] n →ₐ[ℚ_[p]] E :=
  AdjoinRoot.liftAlgHom
    ((cyclotomicLubinDatum p).reducedPolynomial ℚ_[p] n)
    (Algebra.ofId ℚ_[p] E)
    (IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E - 1)
    (by
      simpa [Polynomial.aeval_def] using
        (padic_zeta_reduced p n E))

@[simp]
theorem padic_alg_hom
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E] :
    padicAlgHom p n E
        ((cyclotomicLubinDatum p).root ℚ_[p] n) =
      IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E - 1 := by
  exact AdjoinRoot.liftAlgHom_root _ _ _ _

/-- The translated primitive root generates the cyclotomic extension, so
the canonical root-field homomorphism is onto. -/
theorem padic_alg_surjective
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E] :
    Function.Surjective
      (padicAlgHom p n E) := by
  let zeta := IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E
  let hzetaprim := IsCyclotomicExtension.zeta_spec
    (p ^ (n + 1)) ℚ_[p] E
  have hadjoin : Algebra.adjoin ℚ_[p] ({zeta - 1} : Set E) = ⊤ := by
    simpa only [IsPrimitiveRoot.subOnePowerBasis_gen] using
      (hzetaprim.subOnePowerBasis ℚ_[p]).adjoin_gen_eq_top
  rw [← AlgHom.range_eq_top]
  apply top_unique
  rw [← hadjoin]
  apply Algebra.adjoin_le
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst x
  refine ⟨(cyclotomicLubinDatum p).root ℚ_[p] n, ?_⟩
  exact padic_alg_hom p n E

/-- The abstract finite Lubin--Tate root field is canonically the
`p^(n+1)`-cyclotomic extension, with root coordinate `pi_(n+1) = zeta-1`. -/
noncomputable def padicCyclotomicRoot
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E] :
    (cyclotomicLubinDatum p).RootField ℚ_[p] n ≃ₐ[ℚ_[p]] E :=
  AlgEquiv.ofBijective
    (padicAlgHom p n E)
    ⟨(padicAlgHom p n E).injective,
      padic_alg_surjective p n E⟩

@[simp]
theorem padic_cyclotomic_root
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E] :
    padicCyclotomicRoot p n E
        ((cyclotomicLubinDatum p).root ℚ_[p] n) =
      IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E - 1 :=
  padic_alg_hom p n E

/-- Cyclotomic realization of the root field for the valuation-integer
presentation required by the generic local-field theorems. -/
noncomputable def padicCyclotomicAlg
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E] :
    (padicLubinDatum p).RootField ℚ_[p] n ≃ₐ[ℚ_[p]] E :=
  (padicIntegerAlg p n).trans
    (padicCyclotomicRoot p n E)

@[simp]
theorem padic_cyclotomic_alg
    (p : ℕ) [Fact p.Prime] (n : ℕ)
    (E : Type*) [Field E] [Algebra ℚ_[p] E]
    [IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] E] :
    padicCyclotomicAlg p n E
        ((padicLubinDatum p).root ℚ_[p] n) =
      IsCyclotomicExtension.zeta (p ^ (n + 1)) ℚ_[p] E - 1 := by
  simp [padicCyclotomicAlg]

end

end Towers.CField.LTate

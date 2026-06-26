import Submission.ClassField.LubinTate.PadicUniformizerChange

/-!
# The basic Lubin--Tate datum for a unit multiple of `p`

For a `p`-adic unit `u`, this packages the polynomial
`(p * u) X + X ^ p` as a polynomial Lubin--Tate datum.  It is the second
finite tower used in the uniformizer-independence argument: its chosen
uniformizer `p * u` is therefore a norm at every finite level.
-/

namespace Submission.CField.LTate

open Polynomial
open Submission.CField.FGroups

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The basic Lubin--Tate datum belonging to the prime element `p * u`. -/
noncomputable def padicTateDatum (u : ℤ_[p]ˣ) :
    LTDatum ℤ_[p] where
  pi := (p : ℤ_[p]) * (u : ℤ_[p])
  q := p
  residueCard := by
    have hspan : Ideal.span {((p : ℤ_[p]) * (u : ℤ_[p]))} =
        Ideal.span {(p : ℤ_[p])} :=
      Ideal.span_singleton_mul_right_unit u.isUnit (p : ℤ_[p])
    rw [hspan, Nat.card_eq_fintype_card]
    exact padic_int_card p
  f := basicLubinTate ((p : ℤ_[p]) * (u : ℤ_[p])) p
  pi_irreducible := by
    rw [irreducible_mul_units]
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    exact PadicInt.maximalIdeal_eq_span_p
  f_monic := basic_lubin_monic _ (Fact.out : p.Prime).one_lt
  f_natDegree :=
    basic_lubin_degree _ (Fact.out : p.Prime).one_lt
  one_lt_q := (Fact.out : p.Prime).one_lt
  lubinTateSeries :=
    lubin_tate_basic _ (Fact.out : p.Prime).one_lt

@[simp]
theorem lubin_datum_pi (u : ℤ_[p]ˣ) :
    (padicTateDatum p u).pi =
      (p : ℤ_[p]) * (u : ℤ_[p]) :=
  rfl

/-- The basic datum for the uniformizer `p * u`, transported to the
valuation-integer presentation used by the generic local-field Lubin--Tate
theorems. -/
noncomputable def lubinTateDatum (u : ℤ_[p]ˣ) :
    LTDatum
      (Valuation.integer (NormedField.valuation (K := ℚ_[p]))) := by
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let e : A ≃+* ℤ_[p] := padicNormInt p
  let D := padicTateDatum p u
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

/-- The residue quotient for the basic valuation-integer datum is the usual
residue quotient of `ℤ_[p]`. -/
noncomputable def padicResidueInt
    (u : ℤ_[p]ˣ) :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := lubinTateDatum p u
    (A ⧸ Ideal.span {D.pi}) ≃+*
      (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) := by
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let e : A ≃+* ℤ_[p] := padicNormInt p
  let D := lubinTateDatum p u
  let I : Ideal A := Ideal.span {D.pi}
  let J : Ideal ℤ_[p] := Ideal.span {(p : ℤ_[p])}
  have hIJ : J = I.map e.toRingHom := by
    change Ideal.span {(p : ℤ_[p])} =
      (Ideal.span {e.symm ((p : ℤ_[p]) * (u : ℤ_[p]))}).map e.toRingHom
    rw [Ideal.map_span]
    simp only [Set.image_singleton]
    exact (Ideal.span_singleton_mul_right_unit u.isUnit (p : ℤ_[p])).symm
  exact Ideal.quotientEquiv I J e hIJ

/-- The residue quotient of the transported basic datum is a field. -/
theorem padic_integer_field (u : ℤ_[p]ˣ) :
    let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
    let D := lubinTateDatum p u
    IsField (A ⧸ Ideal.span {D.pi}) := by
  exact (padicResidueInt p u).toMulEquiv.isField
    (padic_int_field p)

/-- Transporting the basic datum to valuation integers does not change its
reduced polynomial after extending coefficients to `ℚ_[p]`. -/
theorem padic_datum_reduced
    (u : ℤ_[p]ˣ) (n : ℕ) :
    (lubinTateDatum p u).reducedPolynomial ℚ_[p] n =
      (padicTateDatum p u).reducedPolynomial ℚ_[p] n := by
  let A := Valuation.integer (NormedField.valuation (K := ℚ_[p]))
  let e : A ≃+* ℤ_[p] := padicNormInt p
  let D := padicTateDatum p u
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

/-- The abstract basic root fields in the two integer-ring presentations are
canonically equivalent. -/
noncomputable def padicIntegerBasic
    (u : ℤ_[p]ˣ) (n : ℕ) :
    (lubinTateDatum p u).RootField ℚ_[p] n ≃ₐ[ℚ_[p]]
      (padicTateDatum p u).RootField ℚ_[p] n :=
  AdjoinRoot.algEquivOfEq ℚ_[p]
    ((lubinTateDatum p u).reducedPolynomial ℚ_[p] n)
    ((padicTateDatum p u).reducedPolynomial ℚ_[p] n)
    (padic_datum_reduced p u n)

@[simp]
theorem padic_integer_basic
    (u : ℤ_[p]ˣ) (n : ℕ) :
    padicIntegerBasic p u n
        ((lubinTateDatum p u).root ℚ_[p] n) =
      (padicTateDatum p u).root ℚ_[p] n := by
  exact AdjoinRoot.algEquivOfEq_root _ _ _

end

end Submission.CField.LTate

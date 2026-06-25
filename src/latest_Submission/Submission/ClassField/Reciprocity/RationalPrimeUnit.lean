import Submission.ClassField.Ideles.IdeleClassNorm
import Submission.ClassField.Ideles.IdeleIdealMap
import Submission.ClassField.Ideles.LocalPlaceEmbeddings
import Submission.ClassField.Reciprocity.LocalFactorsQ
import Submission.ClassField.Reciprocity.RationalUniqueness

/-!
# Chapter V, Section 5, Lemma 5.9

This file builds the rational normalizing factor used in the full idèle
decomposition.  The finite part is obtained by multiplying the rational
primes with the exponents read from the finite idèle.
-/

namespace Submission.CField.Recip

open Filter IsDedekindDomain NumberField Topology
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open scoped RestrictedProduct

noncomputable section

local instance : DecidableEq (HeightOneSpectrum ℤ) := Classical.decEq _

/-- The rational prime attached to a finite place, regarded as a nonzero
rational number. -/
private def rationalPrimeUnit (v : HeightOneSpectrum ℤ) : ℚˣ :=
  Units.mk0 (Rat.HeightOneSpectrum.natGenerator v : ℚ) <| by
    exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero

/-- Multiply the rational primes according to a finitely supported integral
exponent vector. -/
private noncomputable def rationalExponentHom :
    Multiplicative (HeightOneSpectrum ℤ →₀ ℤ) →* ℚˣ :=
  AddMonoidHom.toMultiplicative <|
    Finsupp.liftAddHom fun v =>
      zmultiplesHom (Additive ℚˣ) (Additive.ofMul (rationalPrimeUnit v))

private theorem rational_exponent_single
    (v : HeightOneSpectrum ℤ) (n : ℤ) :
    rationalExponentHom
        (Multiplicative.ofAdd (Finsupp.single v n)) =
      rationalPrimeUnit v ^ n := by
  change Additive.toMul
      (Finsupp.liftAddHom (fun w =>
        zmultiplesHom (Additive ℚˣ) (Additive.ofMul (rationalPrimeUnit w)))
          (Finsupp.single v n)) = _
  rw [Finsupp.liftAddHom_apply_single]
  rfl

private theorem span_nat_self (v : HeightOneSpectrum ℤ) :
    Ideal.span ({(Rat.HeightOneSpectrum.natGenerator v : ℤ)} : Set ℤ) =
      v.asIdeal := by
  have hint : Rat.IsIntegralClosure.intEquiv ℤ = RingEquiv.refl ℤ := by
    ext n
    simp
  calc
    Ideal.span ({(Rat.HeightOneSpectrum.natGenerator v : ℤ)} : Set ℤ) =
        v.asIdeal.map (Rat.IsIntegralClosure.intEquiv ℤ) :=
      Rat.HeightOneSpectrum.span_natGenerator v
    _ = v.asIdeal := by
      rw [hint]
      change v.asIdeal.map (RingHom.id ℤ) = v.asIdeal
      exact v.asIdeal.map_id

private theorem int_valuation_generator
    (v w : HeightOneSpectrum ℤ) :
    w.intValuation (Rat.HeightOneSpectrum.natGenerator v : ℤ) =
      if w = v then WithZero.exp (-1 : ℤ) else 1 := by
  classical
  split_ifs with hwv
  · subst w
    apply v.intValuation_singleton
    · exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator v).ne_zero
    · exact (span_nat_self v).symm
  · apply w.intValuation_eq_one_iff.mpr
    intro hmem
    have hdvd : Rat.HeightOneSpectrum.natGenerator w ∣
        Rat.HeightOneSpectrum.natGenerator v := by
      have hdvdInt : (Rat.HeightOneSpectrum.natGenerator w : ℤ) ∣
          (Rat.HeightOneSpectrum.natGenerator v : ℤ) := by
        rw [← Ideal.mem_span_singleton]
        rw [span_nat_self]
        exact hmem
      exact_mod_cast hdvdInt
    have heq : Rat.HeightOneSpectrum.natGenerator w =
        Rat.HeightOneSpectrum.natGenerator v := by
      rcases (Rat.HeightOneSpectrum.prime_natGenerator v).eq_one_or_self_of_dvd
        _ hdvd with hone | hself
      · exact False.elim
          ((Rat.HeightOneSpectrum.prime_natGenerator w).ne_one hone)
      · exact hself
    apply hwv
    apply Rat.HeightOneSpectrum.primesEquiv.injective
    exact Subtype.ext heq

private theorem valuation_rational_unit
    (v w : HeightOneSpectrum ℤ) :
    w.valuation ℚ (rationalPrimeUnit v : ℚ) =
      if w = v then WithZero.exp (-1 : ℤ) else 1 := by
  classical
  rw [show (rationalPrimeUnit v : ℚ) =
      algebraMap ℤ ℚ (Rat.HeightOneSpectrum.natGenerator v : ℤ) by rfl,
    w.valuation_of_algebraMap]
  exact int_valuation_generator v w

private theorem valuation_rational_hom
    (e : HeightOneSpectrum ℤ →₀ ℤ) (w : HeightOneSpectrum ℤ) :
    w.valuation ℚ (rationalExponentHom (Multiplicative.ofAdd e) : ℚ) =
      WithZero.exp (-e w) := by
  classical
  induction e using Finsupp.induction with
  | zero => simp
  | @single_add v n e hv hn ih =>
      rw [ofAdd_add, map_mul, rational_exponent_single,
        Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, ih,
        valuation_rational_unit]
      by_cases hvw : w = v
      · subst w
        simp only [ite_true, Finsupp.add_apply, Finsupp.single_eq_same]
        rw [← WithZero.exp_zsmul, Int.zsmul_eq_mul]
        simp only [mul_neg, mul_one]
        rw [← WithZero.exp_add]
        congr 1
        omega
      · have hvw' : v ≠ w := fun h => hvw h.symm
        simp [hvw]

/-- The positive rational factor whose finite valuations agree with a finite
idèle. -/
noncomputable def rationalFiniteNormalizer :
    FiniteIdeles ℤ ℚ →* ℚˣ :=
  rationalExponentHom.comp (ideleExponentHom ℤ ℚ)

private theorem principal_idele_int
    (x : ℚˣ) (P : HeightOneSpectrum ℤ) :
    (principalIdele ℤ ℚ x).2.1 P =
      Units.map (algebraMap ℚ (P.adicCompletion ℚ)) x := by
  apply Units.ext
  rfl

theorem exponent_rational_normalizer
    (a : FiniteIdeles ℤ ℚ) :
    ideleExponentHom ℤ ℚ
        (principalIdele ℤ ℚ (rationalFiniteNormalizer a)).2 =
      ideleExponentHom ℤ ℚ a := by
  apply Multiplicative.toAdd.injective
  apply Finsupp.ext
  intro v
  rw [show (ideleExponentHom ℤ ℚ
      (principalIdele ℤ ℚ (rationalFiniteNormalizer a)).2).toAdd v =
      -WithZero.log (Valued.v
        ((((principalIdele ℤ ℚ (rationalFiniteNormalizer a)).2.1 v :
          (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ))) by
      exact idele_exponent_hom ℤ ℚ _ v]
  have hcoord :
      (((principalIdele ℤ ℚ (rationalFiniteNormalizer a)).2.1 v :
          (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
        algebraMap ℚ (v.adicCompletion ℚ) (rationalFiniteNormalizer a : ℚ) :=
    congrArg Units.val
      (principal_idele_int
        (rationalFiniteNormalizer a) v)
  rw [hcoord]
  change -WithZero.log (Valued.v
    (algebraMap ℚ (v.adicCompletion ℚ) (rationalFiniteNormalizer a : ℚ))) = _
  rw [show Valued.v
      (algebraMap ℚ (v.adicCompletion ℚ) (rationalFiniteNormalizer a : ℚ)) =
        v.valuation ℚ (rationalFiniteNormalizer a : ℚ) from
      v.valuedAdicCompletion_eq_valuation' _]
  rw [show rationalFiniteNormalizer a =
      rationalExponentHom (ideleExponentHom ℤ ℚ a) from rfl]
  rw [show v.valuation ℚ
      (rationalExponentHom (ideleExponentHom ℤ ℚ a) : ℚ) =
        WithZero.exp (-(ideleExponentHom ℤ ℚ a).toAdd v) by
      simpa using valuation_rational_hom
        (ideleExponentHom ℤ ℚ a).toAdd v]
  simp

/-- Dividing a finite idèle by its rational normalizing factor leaves a
unit at every finite place. -/
theorem normalizer_inv_everywhere
    (a : FiniteIdeles ℤ ℚ) :
    (principalIdele ℤ ℚ (rationalFiniteNormalizer a)⁻¹).2 * a ∈
      everywhereUnitIdeles ℤ ℚ := by
  rw [← idele_ideal_ker, MonoidHom.mem_ker, map_mul, map_inv]
  have hmap : finiteIdeleIdeal ℤ ℚ
      (principalIdele ℤ ℚ (rationalFiniteNormalizer a)).2 =
      finiteIdeleIdeal ℤ ℚ a := by
    unfold finiteIdeleIdeal
    change (fractionalIdealFactorization ℤ ℚ)
        (ideleExponentHom ℤ ℚ
          (principalIdele ℤ ℚ (rationalFiniteNormalizer a)).2) =
      (fractionalIdealFactorization ℤ ℚ)
        (ideleExponentHom ℤ ℚ a)
    rw [exponent_rational_normalizer]
  change finiteIdeleIdeal ℤ ℚ
      ((principalIdele ℤ ℚ (rationalFiniteNormalizer a)).2⁻¹) *
      finiteIdeleIdeal ℤ ℚ a = 1
  rw [map_inv, hmap, inv_mul_cancel]

/-- A copy of `ℚˣ` carrying the discrete topology specified in the source. -/
def DiscreteRationalUnits := ℚˣ

instance : CommGroup DiscreteRationalUnits := inferInstanceAs (CommGroup ℚˣ)

instance : TopologicalSpace DiscreteRationalUnits := ⊥

instance : DiscreteTopology DiscreteRationalUnits :=
  discreteTopology_bot DiscreteRationalUnits

instance : IsTopologicalGroup DiscreteRationalUnits :=
  inferInstance

/-- Forget the deliberately discrete topology on the rational factor. -/
def discreteRationalUnits : DiscreteRationalUnits ≃* ℚˣ :=
  MulEquiv.refl ℚˣ

/-- The positive component of the unique infinite completion of `ℚ`. -/
def RationalPositiveUnits :
    Subgroup Rat.infinitePlace.Completionˣ :=
  (Units.posSubgroup ℝ).comap
    (Units.map rationalInfiniteCompletion.toMonoidHom)

private def realUnitSign (x : ℝˣ) : ℚˣ :=
  if 0 < (x : ℝ) then 1 else -1

private theorem real_sign_mul (x y : ℝˣ) :
    realUnitSign (x * y) =
      realUnitSign x * realUnitSign y := by
  by_cases hx : 0 < (x : ℝ)
  · by_cases hy : 0 < (y : ℝ)
    · simp [realUnitSign, hx, hy, mul_pos hx hy]
    · have hyneg : (y : ℝ) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hy) y.ne_zero
      have hxyneg : ((x * y : ℝˣ) : ℝ) < 0 := mul_neg_of_pos_of_neg hx hyneg
      simp [realUnitSign, hx, hy]
  · have hxneg : (x : ℝ) < 0 :=
      lt_of_le_of_ne (le_of_not_gt hx) x.ne_zero
    by_cases hy : 0 < (y : ℝ)
    · have hxyneg : ((x * y : ℝˣ) : ℝ) < 0 := mul_neg_of_neg_of_pos hxneg hy
      simp [realUnitSign, hx, hy]
    · have hyneg : (y : ℝ) < 0 :=
        lt_of_le_of_ne (le_of_not_gt hy) y.ne_zero
      have hxypos : 0 < ((x * y : ℝˣ) : ℝ) := mul_pos_of_neg_of_neg hxneg hyneg
      simp [realUnitSign, hx, hy]
      simpa using hxypos

/-- The sign of a real unit, valued in the rational units `{±1}`. -/
private def realSignRational : ℝˣ →* ℚˣ where
  toFun := realUnitSign
  map_one' := by simp [realUnitSign]
  map_mul' := real_sign_mul

private theorem real_sign_rational (x : ℝˣ) :
    realSignRational x = 1 ↔ 0 < (x : ℝ) := by
  by_cases hx : 0 < (x : ℝ)
  · simp [realSignRational, realUnitSign, hx]
  · simp [realSignRational, realUnitSign, hx]

/-- Read the unique infinite coordinate of a rational infinite idèle. -/
private def rationalInfiniteHom :
    (InfiniteAdeleRing ℚ)ˣ →* Rat.infinitePlace.Completionˣ where
  toFun x := ContinuousMulEquiv.piUnits x Rat.infinitePlace
  map_one' := by
    exact congrFun (map_one (ContinuousMulEquiv.piUnits.toMulEquiv))
      Rat.infinitePlace
  map_mul' x y := by
    exact congrFun (map_mul (ContinuousMulEquiv.piUnits.toMulEquiv) x y)
      Rat.infinitePlace

/-- The sign of the infinite coordinate of a rational idèle. -/
private def rationalInfiniteSign :
    (InfiniteAdeleRing ℚ)ˣ →* ℚˣ :=
  realSignRational.comp <|
    (rationalInfiniteUnits.toMonoidHom.comp
      rationalInfiniteHom)

private theorem rational_exponent_pos
    (e : Multiplicative (HeightOneSpectrum ℤ →₀ ℤ)) :
    0 < (rationalExponentHom e : ℚ) := by
  let f := e.toAdd
  change 0 < (rationalExponentHom (Multiplicative.ofAdd f) : ℚ)
  induction f using Finsupp.induction with
  | zero => simp
  | @single_add v n f hv hn ih =>
      rw [ofAdd_add, map_mul, rational_exponent_single, Units.val_mul,
        Units.val_zpow_eq_zpow_val]
      exact mul_pos (zpow_pos (by
        change (0 : ℚ) < Rat.HeightOneSpectrum.natGenerator v
        exact_mod_cast (Rat.HeightOneSpectrum.prime_natGenerator v).pos) _) ih

private theorem rational_normalizer_pos (a : FiniteIdeles ℤ ℚ) :
    0 < (rationalFiniteNormalizer a : ℚ) :=
  rational_exponent_pos _

private theorem rational_exponent_injective :
    Function.Injective rationalExponentHom := by
  intro e f hef
  apply Multiplicative.toAdd.injective
  apply Finsupp.ext
  intro v
  have hv := congrArg (fun q : ℚˣ => v.valuation ℚ (q : ℚ)) hef
  have he := valuation_rational_hom e.toAdd v
  have hf := valuation_rational_hom f.toAdd v
  change v.valuation ℚ (rationalExponentHom e : ℚ) = _ at he
  change v.valuation ℚ (rationalExponentHom f : ℚ) = _ at hf
  change v.valuation ℚ (rationalExponentHom e : ℚ) =
    v.valuation ℚ (rationalExponentHom f : ℚ) at hv
  rw [he, hf] at hv
  exact neg_injective (WithZero.exp_injective hv)

private theorem rational_normalizer_one
    (a : FiniteIdeles ℤ ℚ) :
    rationalFiniteNormalizer a = 1 ↔
      a ∈ everywhereUnitIdeles ℤ ℚ := by
  rw [← idele_ideal_ker, MonoidHom.mem_ker,
    finiteIdeleIdeal]
  change rationalExponentHom (ideleExponentHom ℤ ℚ a) = 1 ↔
    (fractionalIdealFactorization ℤ ℚ)
      (ideleExponentHom ℤ ℚ a) = 1
  rw [← map_one rationalExponentHom,
    rational_exponent_injective.eq_iff,
    ← map_one (fractionalIdealFactorization ℤ ℚ),
    (fractionalIdealFactorization ℤ ℚ).injective.eq_iff]

/-- The rational factor in Milne's decomposition: its sign is read at the
infinite place and its prime exponents at the finite places. -/
noncomputable def rationalIdeleNormalizer : IdeleGroup ℤ ℚ →* ℚˣ where
  toFun a := rationalInfiniteSign a.1 * rationalFiniteNormalizer a.2
  map_one' := by
    change rationalInfiniteSign 1 * rationalFiniteNormalizer 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' a b := by
    change rationalInfiniteSign (a.1 * b.1) *
      rationalFiniteNormalizer (a.2 * b.2) = _
    rw [map_mul, map_mul]
    ac_rfl

private theorem principal_idele_infinite
    (x : ℚˣ) (v : InfinitePlace ℚ) :
    MulEquiv.piUnits (principalIdele ℤ ℚ x).1 v =
      Units.map (algebraMap ℚ v.Completion) x := by
  apply Units.ext
  rfl

/-- The infinite adele ring of `ℚ` has just one factor, so evaluation at the
unique infinite place is a multiplicative equivalence. -/
noncomputable def rationalInfiniteEquiv :
    (InfiniteAdeleRing ℚ)ˣ ≃* Rat.infinitePlace.Completionˣ :=
  MulEquiv.piUnits.trans <| MulEquiv.piUnique fun v : InfinitePlace ℚ =>
    v.Completionˣ

private theorem principal_val_rat
    (q : ℚˣ)
    (hq : (principalIdele ℤ ℚ q).2 ∈ everywhereUnitIdeles ℤ ℚ)
    (p : Nat.Primes) :
    padicValRat p q = 0 := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  let v : HeightOneSpectrum ℤ := Rat.HeightOneSpectrum.primesEquiv.symm p
  have hv := hq v
  change ((principalIdele ℤ ℚ q).2.1 v) ∈
    (v.adicCompletionIntegers ℚ).units at hv
  rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    at hv
  rw [principal_idele_int] at hv
  change Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (q : ℚ)) = 1 at hv
  have hv' : v.valuation ℚ (q : ℚ) = 1 := by
    rw [← v.valuedAdicCompletion_eq_valuation']
    exact hv
  have hvp : Rat.padicValuation p (q : ℚ) = 1 := by
    have hequiv := Rat.HeightOneSpectrum.valuation_equiv_padicValuation v
    have := hequiv.eq_one_iff_eq_one.mp hv'
    simpa [v] using this
  change (if (q : ℚ) = 0 then 0 else WithZero.exp (-padicValRat p q)) = 1 at hvp
  rw [if_neg q.ne_zero, ← WithZero.exp_zero] at hvp
  exact neg_eq_zero.mp (WithZero.exp_injective hvp)

/-- The elementary uniqueness assertion used by Milne: a positive rational
principal idèle which is a unit at every finite place is `1`. -/
theorem positive_rational_idele
    (q : ℚˣ) (hqpos : 0 < (q : ℚ))
    (hqunit : (principalIdele ℤ ℚ q).2 ∈
      everywhereUnitIdeles ℤ ℚ) :
    q = 1 := by
  apply Units.ext
  exact positive_val_rat (q : ℚ) hqpos
    (principal_val_rat q hqunit)

/-- The three factors occurring on the left hand side of Lemma V.5.9. -/
abbrev RationalDecompositionFactors :=
  DiscreteRationalUnits ×
    (RationalPositiveUnits × everywhereUnitIdeles ℤ ℚ)

/-- Multiplication of a rational principal idèle, a positive infinite
component, and an everywhere-unit finite component. -/
noncomputable def rationalDecompositionHom :
    RationalDecompositionFactors →* IdeleGroup ℤ ℚ := by
  let rationalFactor : RationalDecompositionFactors →* IdeleGroup ℤ ℚ :=
    (principalIdele ℤ ℚ).comp <|
      discreteRationalUnits.toMonoidHom.comp
        (MonoidHom.fst DiscreteRationalUnits
          (RationalPositiveUnits × everywhereUnitIdeles ℤ ℚ))
  let positiveFactor : RationalPositiveUnits →*
      (InfiniteAdeleRing ℚ)ˣ :=
    rationalInfiniteEquiv.symm.toMonoidHom.comp
      (RationalPositiveUnits.subtype)
  let finiteUnitFactor : everywhereUnitIdeles ℤ ℚ →*
      FiniteIdeles ℤ ℚ := (everywhereUnitIdeles ℤ ℚ).subtype
  let remainingFactors :
      RationalPositiveUnits × everywhereUnitIdeles ℤ ℚ →*
        IdeleGroup ℤ ℚ := MonoidHom.prod
      (positiveFactor.comp <| MonoidHom.fst _ _)
      (finiteUnitFactor.comp <| MonoidHom.snd _ _)
  let remainingFactors' : RationalDecompositionFactors →* IdeleGroup ℤ ℚ :=
    remainingFactors.comp <|
      MonoidHom.snd DiscreteRationalUnits
        (RationalPositiveUnits × everywhereUnitIdeles ℤ ℚ)
  exact rationalFactor * remainingFactors'

@[simp]
theorem rational_decomposition_hom
    (x : RationalDecompositionFactors) :
    rationalDecompositionHom x =
      principalIdele ℤ ℚ (discreteRationalUnits x.1) *
        (show IdeleGroup ℤ ℚ from
          (rationalInfiniteEquiv.symm x.2.1.1, x.2.2.1)) := by
  rfl

private theorem rational_infinite_units
    (x : (InfiniteAdeleRing ℚ)ˣ) :
    rationalInfiniteEquiv x = rationalInfiniteHom x := by
  change MulEquiv.piUnits x (default : InfinitePlace ℚ) =
    MulEquiv.piUnits x Rat.infinitePlace
  have h : (default : InfinitePlace ℚ) = Rat.infinitePlace := Subsingleton.elim _ _
  cases h
  rfl

private theorem rational_positive_units
    (x : (InfiniteAdeleRing ℚ)ˣ) :
    rationalInfiniteEquiv x ∈ RationalPositiveUnits ↔
      rationalInfiniteSign x = 1 := by
  rw [rational_infinite_units]
  change Units.map rationalInfiniteCompletion.toMonoidHom
      (rationalInfiniteHom x) ∈ Units.posSubgroup ℝ ↔ _
  rw [Units.mem_posSubgroup]
  exact (real_sign_rational _).symm

private theorem infinite_sign_principal
    (q : ℚˣ) :
    rationalInfiniteSign (principalIdele ℤ ℚ q).1 =
      realSignRational
        (Units.map (algebraMap ℚ ℝ) q) := by
  unfold rationalInfiniteSign
  apply congrArg realSignRational
  apply Units.ext
  change rationalInfiniteCompletion
      ((MulEquiv.piUnits (principalIdele ℤ ℚ q).1 Rat.infinitePlace :
        Rat.infinitePlace.Completionˣ) : Rat.infinitePlace.Completion) =
    algebraMap ℚ ℝ (q : ℚ)
  rw [principal_idele_infinite]
  rw [show (((Units.map (algebraMap ℚ Rat.infinitePlace.Completion) q :
      Rat.infinitePlace.Completionˣ) : Rat.infinitePlace.Completion)) =
      algebraMap ℚ Rat.infinitePlace.Completion (q : ℚ) by rfl]
  have hsource : algebraMap ℚ Rat.infinitePlace.Completion (q : ℚ) =
      ((q : ℚ) : Rat.infinitePlace.Completion) := by
    simp
  have htarget : algebraMap ℚ ℝ (q : ℚ) = ((q : ℚ) : ℝ) := by
    simp
  rw [hsource, htarget]
  exact map_ratCast (f := rationalInfiniteCompletion.toRingHom) (q : ℚ)

private theorem rational_sign_pos
    (q : ℚˣ) (hq : 0 < (q : ℚ)) :
    rationalInfiniteSign (principalIdele ℤ ℚ q).1 = 1 := by
  rw [infinite_sign_principal,
    real_sign_rational]
  simpa using (Rat.cast_pos (K := ℝ)).2 hq

set_option maxHeartbeats 800000 in
-- Dependent restricted-product extensionality needs a larger reduction budget.
/-- The multiplication map in Lemma V.5.9 has unique coordinates. -/
theorem rational_decomposition_injective :
    Function.Injective rationalDecompositionHom := by
  intro x y hxy
  let q : ℚˣ := discreteRationalUnits x.1 *
    (discreteRationalUnits y.1)⁻¹
  let px := principalIdele ℤ ℚ (discreteRationalUnits x.1)
  let py := principalIdele ℤ ℚ (discreteRationalUnits y.1)
  let rx : IdeleGroup ℤ ℚ :=
    (rationalInfiniteEquiv.symm x.2.1.1, x.2.2.1)
  let ry : IdeleGroup ℤ ℚ :=
    (rationalInfiniteEquiv.symm y.2.1.1, y.2.2.1)
  have hxy' : px * rx = py * ry := by
    simpa [px, py, rx, ry] using hxy
  have hprincipal : principalIdele ℤ ℚ q = ry * rx⁻¹ := by
    rw [show q = discreteRationalUnits x.1 *
      (discreteRationalUnits y.1)⁻¹ by rfl, map_mul, map_inv]
    change px * py⁻¹ = ry * rx⁻¹
    calc
      px * py⁻¹ = (px * rx) * (rx⁻¹ * py⁻¹) := by group
      _ = (py * ry) * (rx⁻¹ * py⁻¹) := by rw [hxy']
      _ = (py * py⁻¹) * (ry * rx⁻¹) := by ac_rfl
      _ = ry * rx⁻¹ := by rw [mul_inv_cancel, one_mul]
  have hfinite : (principalIdele ℤ ℚ q).2 ∈
      everywhereUnitIdeles ℤ ℚ := by
    have heq : (principalIdele ℤ ℚ q).2 =
        y.2.2.1 * (x.2.2.1)⁻¹ := congrArg Prod.snd hprincipal
    rw [heq]
    exact Subgroup.mul_mem _ y.2.2.2 (Subgroup.inv_mem _ x.2.2.2)
  have hinfinite : rationalInfiniteEquiv (principalIdele ℤ ℚ q).1 ∈
      RationalPositiveUnits := by
    have heq : rationalInfiniteEquiv (principalIdele ℤ ℚ q).1 =
        y.2.1.1 * (x.2.1.1)⁻¹ := by
      have hfst := congrArg Prod.fst hprincipal
      change rationalInfiniteEquiv (principalIdele ℤ ℚ q).1 = _
      rw [hfst]
      change rationalInfiniteEquiv
        (rationalInfiniteEquiv.symm y.2.1.1 *
          (rationalInfiniteEquiv.symm x.2.1.1)⁻¹) = _
      rw [map_mul, map_inv, MulEquiv.apply_symm_apply,
        MulEquiv.apply_symm_apply]
    rw [heq]
    exact Subgroup.mul_mem _ y.2.1.2 (Subgroup.inv_mem _ x.2.1.2)
  have hqsign : rationalInfiniteSign (principalIdele ℤ ℚ q).1 = 1 :=
    (rational_positive_units _).mp hinfinite
  have hqreal : 0 < algebraMap ℚ ℝ (q : ℚ) := by
    rw [infinite_sign_principal,
      real_sign_rational] at hqsign
    exact hqsign
  have hqpos : 0 < (q : ℚ) := (Rat.cast_pos (K := ℝ)).mp hqreal
  have hqone : q = 1 := positive_rational_idele q hqpos hfinite
  have hfirst : x.1 = y.1 := by
    apply discreteRationalUnits.injective
    change discreteRationalUnits x.1 *
      (discreteRationalUnits y.1)⁻¹ = 1 at hqone
    calc
      discreteRationalUnits x.1 =
          (discreteRationalUnits x.1 *
            (discreteRationalUnits y.1)⁻¹) *
              discreteRationalUnits y.1 := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = discreteRationalUnits y.1 := by rw [hqone, one_mul]
  have hr : rx = ry := by
    apply mul_left_cancel (a := px)
    simpa [px, py, hfirst] using hxy'
  have hinf : x.2.1 = y.2.1 := by
    apply Subtype.ext
    apply rationalInfiniteEquiv.symm.injective
    exact congrArg Prod.fst hr
  have hfin : x.2.2 = y.2.2 := by
    apply Subtype.ext
    exact congrArg Prod.snd hr
  exact Prod.ext hfirst (Prod.ext hinf hfin)

private theorem sign_or_neg
    (x : (InfiniteAdeleRing ℚ)ˣ) :
    rationalInfiniteSign x = 1 ∨ rationalInfiniteSign x = -1 := by
  unfold rationalInfiniteSign realSignRational realUnitSign
  by_cases h : 0 < ((rationalInfiniteUnits
    (rationalInfiniteHom x) : ℝˣ) : ℝ)
  · left
    simp [h]
  · right
    simp [h]

private theorem principal_sign_unit
    (s : ℚˣ) (hs : s = 1 ∨ s = -1) :
    (principalIdele ℤ ℚ s).2 ∈ everywhereUnitIdeles ℤ ℚ := by
  rcases hs with rfl | rfl
  · exact (everywhereUnitIdeles ℤ ℚ).one_mem
  · intro v
    change ((principalIdele ℤ ℚ (-1 : ℚˣ)).2.1 v) ∈
      (v.adicCompletionIntegers ℚ).units
    rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      principal_idele_int]
    change Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (-1 : ℚ)) = 1
    simp

private theorem rational_sign_principal
    (s : ℚˣ) (hs : s = 1 ∨ s = -1) :
    rationalInfiniteSign (principalIdele ℤ ℚ s).1 = s := by
  rcases hs with rfl | rfl
  · have hp : (principalIdele ℤ ℚ (1 : ℚˣ)).1 = 1 :=
      congrArg Prod.fst (map_one (principalIdele ℤ ℚ))
    rw [hp, map_one]
  · rw [infinite_sign_principal]
    apply Units.ext
    norm_num [realSignRational, realUnitSign]

set_option maxHeartbeats 800000 in
-- Constructing all finite and infinite coordinates needs extra elaboration.
/-- Every rational idèle has the decomposition displayed by Milne. -/
theorem rational_decomposition_surjective :
    Function.Surjective rationalDecompositionHom := by
  intro a
  let s : ℚˣ := rationalInfiniteSign a.1
  let r : ℚˣ := rationalFiniteNormalizer a.2
  let q : ℚˣ := s * r
  let b : IdeleGroup ℤ ℚ := principalIdele ℤ ℚ q⁻¹ * a
  have hs : s = 1 ∨ s = -1 := sign_or_neg a.1
  have hsunit : (principalIdele ℤ ℚ s).2 ∈
      everywhereUnitIdeles ℤ ℚ := principal_sign_unit s hs
  have hrunit : (principalIdele ℤ ℚ r⁻¹).2 * a.2 ∈
      everywhereUnitIdeles ℤ ℚ := by
    exact normalizer_inv_everywhere a.2
  have hbfinite : b.2 ∈ everywhereUnitIdeles ℤ ℚ := by
    have hb : b.2 = (principalIdele ℤ ℚ s⁻¹).2 *
        ((principalIdele ℤ ℚ r⁻¹).2 * a.2) := by
      change (principalIdele ℤ ℚ (s * r)⁻¹).2 * a.2 = _
      rw [show (s * r)⁻¹ = s⁻¹ * r⁻¹ by
        rw [mul_inv_rev]
        ac_rfl, map_mul]
      change ((principalIdele ℤ ℚ s⁻¹).2 *
        (principalIdele ℤ ℚ r⁻¹).2) * a.2 = _
      exact mul_assoc _ _ _
    rw [hb]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hsunit) hrunit
  have hsignq : rationalInfiniteSign (principalIdele ℤ ℚ q).1 = s := by
    change rationalInfiniteSign (principalIdele ℤ ℚ (s * r)).1 = s
    rw [map_mul]
    change rationalInfiniteSign
      ((principalIdele ℤ ℚ s).1 * (principalIdele ℤ ℚ r).1) = s
    rw [map_mul, rational_sign_principal s hs,
      rational_sign_pos r (rational_normalizer_pos a.2),
      mul_one]
  have hbinfinite : rationalInfiniteEquiv b.1 ∈
      RationalPositiveUnits := by
    apply (rational_positive_units b.1).mpr
    change rationalInfiniteSign ((principalIdele ℤ ℚ q⁻¹ * a).1) = 1
    change rationalInfiniteSign ((principalIdele ℤ ℚ q⁻¹).1 * a.1) = 1
    have hpq : (principalIdele ℤ ℚ q⁻¹).1 =
        ((principalIdele ℤ ℚ q).1)⁻¹ :=
      congrArg Prod.fst (map_inv (principalIdele ℤ ℚ) q)
    rw [map_mul, hpq, map_inv, hsignq]
    change s⁻¹ * s = 1
    exact inv_mul_cancel _
  let t : RationalPositiveUnits :=
    ⟨rationalInfiniteEquiv b.1, hbinfinite⟩
  let u : everywhereUnitIdeles ℤ ℚ := ⟨b.2, hbfinite⟩
  refine ⟨(q, t, u), ?_⟩
  rw [rational_decomposition_hom]
  change principalIdele ℤ ℚ q *
      (show IdeleGroup ℤ ℚ from
        (rationalInfiniteEquiv.symm (rationalInfiniteEquiv b.1), b.2)) = a
  rw [rationalInfiniteEquiv.symm_apply_apply]
  change principalIdele ℤ ℚ q * b = a
  change principalIdele ℤ ℚ q * (principalIdele ℤ ℚ q⁻¹ * a) = a
  rw [← mul_assoc, ← map_mul]
  rw [mul_inv_cancel, map_one, one_mul]

end

end Submission.CField.Recip

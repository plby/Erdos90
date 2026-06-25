import Towers.ClassField.KummerNormIndex.LocalNorm
import Towers.NumberTheory.Galois.FrobeniusElement
import Towers.NumberTheory.Locals.LocalDegreeFormula

/-!
# The unramified radical case in Proposition VII.6.10

Outside `S ∪ T`, both the radicand and the exponent are units.  The proof
below gives the Appendix A.5 argument directly for the one-generator Galois
extension used in Proposition 6.10.  An inertia element changes the chosen
radical by an `n`th root of unity.  Writing the radical as a quotient of two
local units shows that this root of unity reduces to one; reduction is
injective on `n`th roots of unity because `n` is a unit.  Thus inertia fixes
the generator, so it is trivial and the ramification index is one.
-/

namespace Towers.CField.KNIndex

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- Reduction modulo a prime is injective on `n`th roots of unity when the
residue characteristic does not divide `n`. -/
private theorem one_pow_quotient
    {B : Type*} [CommRing B] [IsDomain B]
    (Q : Ideal B) [Q.IsPrime]
    {n : ℕ} {z : B}
    (hnQ : (n : B) ∉ Q) (hz : z ^ n = 1)
    (hzres : Ideal.Quotient.mk Q z = Ideal.Quotient.mk Q 1) :
    z = 1 := by
  let s : B := ∑ i ∈ Finset.range n, z ^ i
  have hmul : (z - 1) * s = 0 := by
    rw [show (z - 1) * s = z ^ n - 1 by
      exact mul_geom_sum z n]
    rw [hz, sub_self]
  have hsres : Ideal.Quotient.mk Q s = (n : B ⧸ Q) := by
    rw [map_sum]
    simp only [map_pow, hzres, map_one, one_pow]
    simp
  have hnres : (n : B ⧸ Q) ≠ 0 := by
    change Ideal.Quotient.mk Q (n : B) ≠ 0
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hnQ
  have hs : s ≠ 0 := by
    intro hs0
    have : Ideal.Quotient.mk Q s = 0 := by rw [hs0, map_zero]
    rw [hsres] at this
    exact hnres this
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hs)

/-- An element of valuation one is a quotient of two global integers which
are both units at the chosen prime. -/
private theorem unit_fraction_representation
    (L : Type u) [Field L] [NumberField L]
    (Q : FinitePrime L) (alpha : L)
    (halpha : Q.valuation L alpha = 1) :
    ∃ x y : OK L, x ∉ Q.asIdeal ∧ y ∉ Q.asIdeal ∧
      alpha * algebraMap (OK L) L y = algebraMap (OK L) L x := by
  obtain ⟨a, d, h | h⟩ := Q.exists_primeCompl_mul_eq_or_mul_eq alpha
  · have hdval : Q.valuation L (algebraMap (OK L) L d) = 1 := by
      rw [Q.valuation_of_algebraMap (K := L), Q.intValuation_eq_one_iff]
      exact d.property
    have haval : Q.valuation L (algebraMap (OK L) L a) = 1 := by
      rw [← h, map_mul, halpha, hdval, one_mul]
    have ha : a ∉ Q.asIdeal := by
      rw [← Q.intValuation_eq_one_iff,
        ← Q.valuation_of_algebraMap (K := L)]
      exact haval
    exact ⟨a, d, ha, d.property, h⟩
  · have hdval : Q.valuation L (algebraMap (OK L) L d) = 1 := by
      rw [Q.valuation_of_algebraMap (K := L), Q.intValuation_eq_one_iff]
      exact d.property
    have haval : Q.valuation L (algebraMap (OK L) L a) = 1 := by
      have hval := congrArg (Q.valuation L) h
      rw [map_mul, halpha, one_mul, hdval] at hval
      exact hval
    have ha : a ∉ Q.asIdeal := by
      rw [← Q.intValuation_eq_one_iff,
        ← Q.valuation_of_algebraMap (K := L)]
      exact haval
    exact ⟨d, a, d.property, ha, h⟩

/-- Every inertia element fixes a local-unit radical when the exponent is a
unit at the upper prime. -/
theorem inertia_fixes_radical
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : n ≠ 0) (b : Kˣ) (alpha : L)
    (halphaPow : alpha ^ n = algebraMap K L (b : K))
    (Q : FinitePrime L)
    (hnQ : (n : OK L) ∉ Q.asIdeal)
    (halphaVal : Q.valuation L alpha = 1)
    (sigma : Q.asIdeal.inertia Gal(L/K)) :
    (sigma : Gal(L/K)) alpha = alpha := by
  have halpha0 : alpha ≠ 0 := by
    intro h
    have hb0 : algebraMap K L (b : K) = 0 := by
      rw [← halphaPow, h, zero_pow hn]
    exact (map_ne_zero (algebraMap K L)).2 (Units.ne_zero b) hb0
  let zeta : L := (sigma : Gal(L/K)) alpha / alpha
  have hzetaPow : zeta ^ n = 1 := by
    dsimp only [zeta]
    rw [div_pow, ← map_pow, halphaPow,
      (sigma : Gal(L/K)).commutes, div_self]
    exact (map_ne_zero (algebraMap K L)).2 (Units.ne_zero b)
  have hzetaIntegral : IsIntegral ℤ zeta :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (hzetaPow ▸ isIntegral_one)
  let z : OK L := ⟨zeta, hzetaIntegral⟩
  obtain ⟨x, y, hxQ, hyQ, hxy⟩ :=
    unit_fraction_representation L Q alpha halphaVal
  have hxySigma :
      (sigma : Gal(L/K)) alpha *
          algebraMap (OK L) L ((sigma : Gal(L/K)) • y) =
        algebraMap (OK L) L ((sigma : Gal(L/K)) • x) := by
    have h := congrArg (sigma : Gal(L/K)) hxy
    simpa only [map_mul] using h
  have hfield :
      algebraMap (OK L) L (z * x * ((sigma : Gal(L/K)) • y)) =
        algebraMap (OK L) L (((sigma : Gal(L/K)) • x) * y) := by
    simp only [map_mul]
    change zeta * algebraMap (OK L) L x *
        algebraMap (OK L) L ((sigma : Gal(L/K)) • y) =
      algebraMap (OK L) L ((sigma : Gal(L/K)) • x) *
        algebraMap (OK L) L y
    rw [show algebraMap (OK L) L x =
          alpha * algebraMap (OK L) L y from hxy.symm,
      show algebraMap (OK L) L ((sigma : Gal(L/K)) • x) =
          (sigma : Gal(L/K)) alpha *
            algebraMap (OK L) L ((sigma : Gal(L/K)) • y) from hxySigma.symm]
    dsimp only [zeta]
    field_simp
  have hintegral :
      z * x * ((sigma : Gal(L/K)) • y) =
        ((sigma : Gal(L/K)) • x) * y :=
    NumberField.RingOfIntegers.coe_injective hfield
  have hxres :
      Ideal.Quotient.mk Q.asIdeal ((sigma : Gal(L/K)) • x) =
        Ideal.Quotient.mk Q.asIdeal x := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact sigma.property x
  have hyres :
      Ideal.Quotient.mk Q.asIdeal ((sigma : Gal(L/K)) • y) =
        Ideal.Quotient.mk Q.asIdeal y := by
    rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact sigma.property y
  have hres := congrArg (Ideal.Quotient.mk Q.asIdeal) hintegral
  simp only [map_mul] at hres
  rw [hxres, hyres] at hres
  have hxres0 : Ideal.Quotient.mk Q.asIdeal x ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hxQ
  have hyres0 : Ideal.Quotient.mk Q.asIdeal y ≠ 0 := by
    rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hyQ
  have hzres : Ideal.Quotient.mk Q.asIdeal z =
      Ideal.Quotient.mk Q.asIdeal 1 := by
    apply mul_right_cancel₀ (mul_ne_zero hxres0 hyres0)
    simpa only [map_one, one_mul, mul_assoc] using hres
  have hzpow : z ^ n = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    simpa only [map_pow, map_one] using hzetaPow
  have hz : z = 1 :=
    one_pow_quotient Q.asIdeal hnQ hzpow hzres
  have hzeta : zeta = 1 := by
    simpa only [z, NumberField.RingOfIntegers.coe_injective.eq_iff,
      map_one] using congrArg (algebraMap (OK L) L) hz
  change (sigma : Gal(L/K)) alpha / alpha = 1 at hzeta
  calc
    (sigma : Gal(L/K)) alpha =
        ((sigma : Gal(L/K)) alpha / alpha) * alpha :=
      (div_mul_cancel₀ _ halpha0).symm
    _ = 1 * alpha := by rw [hzeta]
    _ = alpha := one_mul _

/-- A Galois simple radical extension is unramified when its exponent and
radicand both have valuation one. -/
private theorem radical_unramified
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (n : ℕ) (hn : n ≠ 0) (b : Kˣ) (alpha : L)
    (halphaPow : alpha ^ n = algebraMap K L (b : K))
    (hgen : IntermediateField.adjoin K {alpha} = ⊤)
    (P : FinitePrime K) (Q : FinitePrime L)
    (hunder : Q.under (OK K) = P)
    (hnP : P.valuation K (n : K) = 1)
    (hbP : P.valuation K (b : K) = 1) :
    Algebra.IsUnramifiedAt (OK K) Q.asIdeal := by
  letI : P.asIdeal.IsMaximal := P.isMaximal
  letI : Q.asIdeal.IsMaximal := Q.isMaximal
  letI : Q.asIdeal.LiesOver P.asIdeal := by
    refine ⟨?_⟩
    exact (congrArg HeightOneSpectrum.asIdeal hunder).symm
  letI : Field (OK K ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  letI : Field (OK L ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  letI : Finite (OK K ⧸ P.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient P.ne_bot
  letI : Finite (OK L ⧸ Q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient Q.ne_bot
  letI : Algebra.IsSeparable (OK K ⧸ P.asIdeal) (OK L ⧸ Q.asIdeal) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  letI : IsGaloisGroup Gal(L/K) (OK K) (OK L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (OK K) (OK L) K L
  have hnPmem : (n : OK K) ∉ P.asIdeal := by
    rw [← P.intValuation_eq_one_iff,
      ← P.valuation_of_algebraMap (K := K)]
    exact hnP
  have hnQmem : (n : OK L) ∉ Q.asIdeal := by
    intro hnQ
    apply hnPmem
    rw [← hunder]
    change algebraMap (OK K) (OK L) (n : OK K) ∈ Q.asIdeal
    simpa only [map_natCast] using hnQ
  have halphaVal : Q.valuation L alpha = 1 := by
    apply (pow_eq_one_iff_left hn).mp
    rw [← map_pow, halphaPow,
      valuation_ramification_idx P Q, hbP, one_pow]
  have hgenAlg : Algebra.adjoin K {alpha} = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic]
    · have h := congrArg IntermediateField.toSubalgebra hgen
      simpa using h
    · intro x _
      exact IsAlgebraic.of_finite K x
  have hinertia : Q.asIdeal.inertia Gal(L/K) = ⊥ := by
    apply le_antisymm
    · intro sigma hsigma
      rw [Subgroup.mem_bot]
      let sigmaI : Q.asIdeal.inertia Gal(L/K) := ⟨sigma, hsigma⟩
      have hfix : sigma alpha = alpha :=
        inertia_fixes_radical K L n hn b alpha halphaPow Q hnQmem
          halphaVal sigmaI
      have heq : sigma.toAlgHom = (1 : Gal(L/K)).toAlgHom := by
        apply AlgHom.ext_of_adjoin_eq_top hgenAlg
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        simpa only [AlgEquiv.one_apply] using hfix
      exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun heq x
    · exact bot_le
  have hramification :
      Ideal.ramificationIdx P.asIdeal Q.asIdeal = 1 := by
    calc
      Ideal.ramificationIdx P.asIdeal Q.asIdeal =
          Ideal.ramificationIdxIn P.asIdeal (OK L) :=
        (Ideal.ramificationIdxIn_eq_ramificationIdx
          P.asIdeal Q.asIdeal Gal(L/K)).symm
      _ = Nat.card (Q.asIdeal.inertia Gal(L/K)) :=
        (Ideal.card_inertia_eq_ramificationIdxIn
          (G := Gal(L/K)) P.asIdeal P.ne_bot Q.asIdeal).symm
      _ = 1 := by rw [hinertia]; simp
  exact (unramified_ramification_idx
    P.asIdeal Q.asIdeal Q.ne_bot).2 hramification

/-- Value one for the normalized finite absolute value is valuation one. -/
theorem valuation_normalized_value
    (K : Type u) [Field K] [NumberField K]
    (P : FinitePrime K) {x : K}
    (hx : normalizedPlaceValue K (Sum.inl P) x = 1) :
    P.valuation K x = 1 := by
  have hnorm : ‖FinitePlace.embedding P x‖ = 1 := by
    simpa only [normalizedPlaceValue,
      FinitePlace.equivHeightOneSpectrum_symm_apply] using hx
  rw [FinitePlace.norm_embedding'] at hnorm
  have h' :
      WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero P)
          (P.valuation K x) = 1 := by
    exact_mod_cast hnorm
  exact (WithZeroMulInt.toNNReal_eq_one_iff
    (P.valuation K x)
    (HeightOneSpectrum.absNorm_ne_zero P)
    (ne_of_gt (HeightOneSpectrum.one_lt_absNorm_nnreal P))).mp h'

/-- The simple Kummer extension in Proposition VII.6.10 is unramified at
every finite prime outside `S ∪ T`. -/
theorem outsideUnramifiedBridge :
    OutsideUnramifiedBridge.{u} := by
  classical
  intro n K _ _ b S T hDividing hUnit data
  letI : Field data.L := data.fieldL
  letI : NumberField data.L := data.numberFieldL
  letI : Algebra K data.L := data.algebraKL
  letI : FiniteDimensional K data.L := data.finiteDimensionalKL
  letI : IsGalois K data.L := data.isGaloisKL
  intro P hP Q hQunder
  have hPnotS : (Sum.inl P : NumberFieldPlace K) ∉ S := by
    intro hPS
    apply hP
    exact Finset.mem_union_left _ hPS
  have hnValue :
      normalizedPlaceValue K (Sum.inl P) (n : K) = 1 := by
    by_contra hne
    exact hPnotS (hDividing (Sum.inl P) hne)
  have hnP : P.valuation K (n : K) = 1 :=
    valuation_normalized_value K P hnValue
  have hn : n ≠ 0 := by
    intro hn
    subst n
    simp at hnP
  exact radical_unramified K data.L n hn b data.root data.root_pow
    data.adjoin_root_top P Q hQunder hnP (hUnit P hP)

/-- The local-norm bridge of Proposition VII.6.10, now with all three local
cases proved. -/
theorem localNormBridge :
    LocalNormBridge.{u} :=
  bridge_outside_unramified
    outsideUnramifiedBridge

end

end Towers.CField.KNIndex

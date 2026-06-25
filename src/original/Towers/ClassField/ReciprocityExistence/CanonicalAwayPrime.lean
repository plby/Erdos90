import Towers.ClassField.LocalReciprocity.PadicRootCore
import Towers.ClassField.ArtinReciprocity.FrobeniusExamples
import Towers.ClassField.Reciprocity.CompletionArtinHom
import Towers.ClassField.NormIndex.CompletionPlaceComparison
import Towers.ClassField.CyclotomicBrauer.RationalPrimeTransport
import Towers.ClassField.ReciprocityExistence.ExplicitPrimePower
import Towers.ClassField.LocalBrauer.CanonicalUniverseTransport
import Towers.FieldTheory.CentralEmbeddingBrauer
import Towers.NumberTheory.Cyclotomic.GeneralCyclotomic

/-!
# Canonical unramified factors in Example VII.8.2

At a rational prime away from a prime-power cyclotomic conductor, the
canonical Proposition III.3.6 local Artin map is unramified.  This file
identifies its uniformizer value with the global arithmetic Frobenius and
its unit values with the identity.
-/

namespace Towers.CField.RExist

open scoped IsMulCommutative
open AbsoluteValue IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.LFTheory
open Towers.CField.LTate
open Towers.CField.NCorr
open Towers.CField.LRecip
open Towers.CField.LRecip.PNProof
open Towers.CField.ARecip
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.ICohomo
open Towers.CField.NIndex
open Towers.CField.CBrauer
open Towers.CField.LBrauer
open scoped Pointwise

noncomputable section

private theorem rational_height_generator
    (q : ℕ) [Fact q.Prime] :
    Rat.HeightOneSpectrum.natGenerator (rationalHeightOne q) = q :=
  congrArg Subtype.val
    (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply
      (⟨q, Fact.out⟩ : Nat.Primes))

private noncomputable instance padicValuativeRel
    (q : ℕ) [Fact q.Prime] : ValuativeRel ℚ_[q] :=
  ValuativeRel.ofValuation (NormedField.valuation (K := ℚ_[q]))

private instance padicCompatible
    (q : ℕ) [Fact q.Prime] :
    Valuation.Compatible (NormedField.valuation (K := ℚ_[q])) :=
  Valuation.Compatible.ofValuation _

private noncomputable instance padicLocalField
    (q : ℕ) [Fact q.Prime] : IsNonarchimedeanLocalField ℚ_[q] := by
  haveI htop : IsValuativeTopology ℚ_[q] := by
    apply IsValuativeTopology.of_zero
    intro s
    rw [show s ∈ nhds (0 : ℚ_[q]) ↔
        ∃ γ : (MonoidWithZeroHom.ValueGroup₀
            (NormedField.valuation (K := ℚ_[q])))ˣ,
          {x | (NormedField.valuation (K := ℚ_[q])).restrict x < γ.1} ⊆ s from
      (NormedField.toValued (K := ℚ_[q])).is_topological_valuation s]
    simpa using
      (NormedField.valuation (K := ℚ_[q]))
        |>.exists_setOf_restrict_le_iff 0 s
  haveI hnontrivial : ValuativeRel.IsNontrivial ℚ_[q] :=
    (ValuativeRel.isNontrivial_iff_isNontrivial
      (NormedField.valuation (K := ℚ_[q]))).mpr inferInstance
  exact
    { toIsValuativeTopology := htop
      toLocallyCompactSpace := inferInstance
      toIsNontrivial := hnontrivial }

/-- Multiplicative-group form of the canonical absolute-completion
identification with `Q_q`, with all dependent completion instances hidden
inside the definition. -/
noncomputable def rationalAbsoluteUnits
    (q : ℕ) [Fact q.Prime] :
    let P := rationalHeightOne q
    let v := (FinitePlace.mk P).val
    v.Completionˣ ≃* ℚ_[q]ˣ := by
  dsimp only
  let P := rationalHeightOne q
  let v := (FinitePlace.mk P).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : Algebra ℚ v.Completion := (completionEmbedding v).toAlgebra
  exact Units.mapEquiv
    (rationalAbsoluteCompletion q).toRingEquiv.toMulEquiv

/-- The standard rational prime has normalized local-field order one in
`Q_q`. -/
theorem padic_self_order
    (q : ℕ) [Fact q.Prime] :
    localUnitOrder ℚ_[q]
        (Additive.ofMul
          (padicNatUnit q q (Fact.out : q.Prime).ne_zero)) = 1 := by
  apply (local_element_order ℚ_[q]
    (padicNatUnit q q (Fact.out : q.Prime).ne_zero)).mp
  change ValuativeRel.valuation ℚ_[q] (q : ℚ_[q]) =
    ValuativeRel.uniformizer ℚ_[q]
  let v₀ := ValuativeRel.valuation ℚ_[q]
  let vq := NormedField.valuation (K := ℚ_[q])
  have he : v₀.IsEquiv vq := ValuativeRel.isEquiv v₀ vq
  apply le_antisymm
  · apply ValuativeRel.le_uniformizer_iff.mpr
    rw [he.lt_one_iff_lt_one, NormedField.valuation_apply,
      ← NNReal.coe_lt_coe]
    exact_mod_cast Padic.norm_p_lt_one
  · obtain ⟨x, hx⟩ :=
      ValuativeRel.valuation_surjective
        (ValuativeRel.uniformizer ℚ_[q])
    rw [← hx]
    apply he.le_iff_le.mpr
    have hxlt₀ : v₀ x < 1 := by
      rw [hx]
      exact ValuativeRel.uniformizer_lt_one
    have hxlt : vq x < 1 := he.lt_one_iff_lt_one.mp hxlt₀
    rw [NormedField.valuation_apply, NormedField.valuation_apply,
      ← NNReal.coe_le_coe]
    rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe] at hxlt
    change ‖x‖ ≤ ‖(q : ℚ_[q])‖
    rw [Padic.norm_p]
    have hxpow : ‖x‖ < (q : ℝ) ^ (0 : ℤ) := by simpa using hxlt
    rw [Padic.norm_lt_pow_iff_norm_le_pow_sub_one] at hxpow
    simpa using hxpow

/-- Every upper prime over `q ≠ p` in a `p^r`-cyclotomic field is
unramified. -/
theorem cyclotomic_unramified_away
    (p r q : ℕ) [Fact p.Prime] [Fact q.Prime] [NeZero (p ^ r)]
    (hqp : q ≠ p)
    (L : Type) [Field L] [NumberField L]
    [IsCyclotomicExtension {p ^ r} ℚ L]
    [IsGalois ℚ L]
    [IsMulCommutative Gal(L/ℚ)]
    (Q : Ideal (NumberField.RingOfIntegers L)) [Q.IsPrime]
    [Q.LiesOver (rationalHeightOne q).asIdeal] (hQ : Q ≠ ⊥) :
    Algebra.IsUnramifiedAt (NumberField.RingOfIntegers ℚ) Q := by
  letI : IsGalois ℚ L := IsCyclotomicExtension.isGalois {p ^ r} ℚ L
  letI : IsGaloisGroup Gal(L/ℚ)
      (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/ℚ)
      (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers L) ℚ L
  letI : IsGaloisGroup Gal(L/ℚ) ℤ
      (NumberField.RingOfIntegers L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/ℚ) ℤ
      (NumberField.RingOfIntegers L) ℚ L
  apply (unramified_ramification_idx
    (rationalHeightOne q).asIdeal Q hQ).2
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx
      (rationalHeightOne q).asIdeal Q Gal(L/ℚ),
    ramification_idx_span
      (rationalHeightOne q) L,
    rational_height_generator q]
  apply cyclotomic_ramification_dvd
    (n := p ^ r) (p := q) L
  intro hdiv
  have hqpd : q ∣ p := (Fact.out : q.Prime).dvd_of_dvd_pow hdiv
  exact hqp ((Nat.dvd_prime (Fact.out : p.Prime)).mp hqpd |>.resolve_left
    (Fact.out : q.Prime).ne_one)

end

end Towers.CField.RExist

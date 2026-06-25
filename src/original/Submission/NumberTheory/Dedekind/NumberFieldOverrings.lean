import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.KrullDimension.PID


/-!
# Residue fields of Dedekind overrings in number fields

If a Dedekind domain has a number field as its fraction field, then all of its nonzero prime
quotients are finite.  The domain need not be finite as a `ℤ`-module: it may, for example, be a
localization of the ring of integers at an infinite set of primes.

The proof embeds the ring of integers into the given Dedekind overring.  At a nonzero prime, the
two corresponding localizations are valuation subrings of the same number field.  Inclusion and
the one-dimensionality of a discrete valuation ring force those valuation subrings to agree, so
their residue fields are isomorphic.  Finiteness then comes from the usual residue-field theorem
for the ring of integers.
-/

namespace Submission.NumberTheory.Milne

open scoped nonZeroDivisors NumberField

noncomputable section

variable {A K : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
  [Field K] [NumberField K] [Algebra A K] [IsFractionRing A K]

/-- The canonical inclusion of the ring of integers into an integrally closed overring with the
same fraction field. -/
private noncomputable def integersDedekindOverring : 𝓞 K →+* A where
  toFun x := IsIntegralClosure.mk' A (x : K) (x.2.tower_top (A := A))
  map_zero' := by simp
  map_one' := by simp
  map_add' x y := by
    apply IsFractionRing.injective A K
    simp
  map_mul' x y := by
    apply IsFractionRing.injective A K
    simp

omit [NumberField K] in
private lemma integers_dedekind_overring (x : 𝓞 K) :
    algebraMap A K (integersDedekindOverring x) = (x : K) := by
  simp [integersDedekindOverring]

/-- A nonzero ideal of a Dedekind overring contracts nontrivially to the ring of integers. -/
private lemma comap_dedekind_overring (p : Ideal A) (hp : p ≠ ⊥) :
    p.comap (integersDedekindOverring (A := A) (K := K)) ≠ ⊥ := by
  obtain ⟨x, hxp, hx⟩ := p.ne_bot_iff.mp hp
  let z : K := algebraMap A K x
  obtain ⟨n, hn, hnint⟩ := exists_integral_multiples ℤ ℚ ({z} : Finset K)
  have hnint' : IsIntegral ℤ (n • z) := hnint z (by simp)
  let y : 𝓞 K := ⟨n • z, hnint'⟩
  have hy : integersDedekindOverring (A := A) (K := K) y = n • x := by
    apply IsFractionRing.injective A K
    rw [integers_dedekind_overring]
    simp [y, z]
  refine (p.comap (integersDedekindOverring (A := A) (K := K))).ne_bot_iff.mpr
    ⟨y, ?_, ?_⟩
  · change integersDedekindOverring (A := A) (K := K) y ∈ p
    rw [hy]
    exact zsmul_mem hxp n
  · intro h
    have h' := congrArg Subtype.val h
    change n • z = (0 : K) at h'
    exact smul_ne_zero hn ((map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hx) h'

/-- The localizations of the ring of integers and a Dedekind overring at corresponding nonzero
primes are the same valuation subring of their common number field. -/
private noncomputable def localizationDedekindOverring
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    Localization.subalgebra.ofField K
        (p.comap (integersDedekindOverring (A := A) (K := K))).primeCompl
        (p.comap (integersDedekindOverring (A := A) (K := K))).primeCompl_le_nonZeroDivisors ≃+*
      Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors := by
  let f : 𝓞 K →+* A := integersDedekindOverring (A := A) (K := K)
  let q : Ideal (𝓞 K) := p.comap f
  have hq : q ≠ ⊥ := comap_dedekind_overring p hp
  let Oloc := Localization.subalgebra.ofField K q.primeCompl
    q.primeCompl_le_nonZeroDivisors
  let Aloc := Localization.subalgebra.ofField K p.primeCompl
    p.primeCompl_le_nonZeroDivisors
  letI : IsDiscreteValuationRing Oloc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hq Oloc
  letI : IsDiscreteValuationRing Aloc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hp Aloc
  have hle : Oloc.toSubring ≤ Aloc.toSubring := by
    intro x hx
    rcases hx with ⟨a, s, hs, rfl⟩
    refine ⟨f a, f s, ?_, ?_⟩
    · change f s ∉ p
      exact hs
    · dsimp only [f]
      rw [integers_dedekind_overring,
        integers_dedekind_overring]
  have hOVal : ∀ x : K, x ∈ Oloc.toSubring ∨ x⁻¹ ∈ Oloc.toSubring := by
    intro x
    rcases ValuationRing.isInteger_or_isInteger Oloc x with h | h
    · left
      rcases h with ⟨a, ha⟩
      exact ha ▸ a.2
    · right
      rcases h with ⟨a, ha⟩
      exact ha ▸ a.2
  let V : ValuationSubring K := ValuationSubring.ofSubring Oloc.toSubring hOVal
  let W : ValuationSubring K := ValuationSubring.ofLE V Aloc.toSubring hle
  letI : IsDiscreteValuationRing V := by
    change IsDiscreteValuationRing Oloc
    infer_instance
  letI : IsDiscreteValuationRing W := by
    change IsDiscreteValuationRing Aloc
    infer_instance
  have hVW : V ≤ W := fun _ hx ↦ hle hx
  have hWtop : W ≠ ⊤ := by
    intro h
    have hsubTop : Aloc.toSubring = ⊤ := by
      change W.toSubring = ⊤
      rw [h]
      rfl
    let eTop : Aloc ≃+* K :=
      (RingEquiv.subringCongr hsubTop).trans Subring.topEquiv
    exact (IsLocalization.AtPrime.not_isField A hp Aloc)
      (eTop.toMulEquiv.isField (Field.toIsField K))
  have hVW_eq : V = W := V.eq_of_le_of_ne_top hVW hWtop
  have hsub : Oloc.toSubring = Aloc.toSubring :=
    congrArg ValuationSubring.toSubring hVW_eq
  exact RingEquiv.subringCongr hsub

/-- Every nonzero prime quotient of a Dedekind domain whose fraction field is a number field is
finite.  No module-finiteness assumption over `ℤ` is required. -/
theorem fraction_number_field
    {K : Type*} [Field K] [NumberField K] [Algebra A K] [IsFractionRing A K]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) : Finite (A ⧸ p) := by
  let f : 𝓞 K →+* A := integersDedekindOverring (A := A) (K := K)
  let q : Ideal (𝓞 K) := p.comap f
  have hq : q ≠ ⊥ := comap_dedekind_overring p hp
  letI : q.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hq inferInstance
  letI : p.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp inferInstance
  let Oloc := Localization.subalgebra.ofField K q.primeCompl
    q.primeCompl_le_nonZeroDivisors
  let Aloc := Localization.subalgebra.ofField K p.primeCompl
    p.primeCompl_le_nonZeroDivisors
  letI : IsDiscreteValuationRing Oloc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) hq Oloc
  letI : IsDiscreteValuationRing Aloc :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hp Aloc
  let e : Oloc ≃+* Aloc := localizationDedekindOverring p hp
  let eqO : (𝓞 K ⧸ q) ≃+* IsLocalRing.ResidueField Oloc :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal q Oloc
  let eqA : (A ⧸ p) ≃+* IsLocalRing.ResidueField Aloc :=
    IsLocalization.AtPrime.equivQuotMaximalIdeal p Aloc
  let eqRes : IsLocalRing.ResidueField Oloc ≃+* IsLocalRing.ResidueField Aloc :=
    IsLocalRing.ResidueField.mapEquiv e
  let eqTotal : (𝓞 K ⧸ q) ≃ (A ⧸ p) :=
    (eqO.trans eqRes).trans eqA.symm
  exact Finite.of_equiv (𝓞 K ⧸ q) eqTotal

end

end Submission.NumberTheory.Milne

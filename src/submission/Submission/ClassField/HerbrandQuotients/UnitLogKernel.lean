import Submission.ClassField.HerbrandQuotients.UnitLogMap
import Submission.ClassField.NormIndex.CompletionPlaceBridge
import Submission.NumberTheory.Units.BoundedConjugates

/-!
# The kernel of the logarithmic map in Proposition VII.3.1

Milne observes that an element in the kernel has absolute value one at
every place: outside `T` this is the defining property of a `T`-unit, and
on `T` it follows from the vanishing logarithms.  Kronecker's theorem then
identifies the kernel with the roots of unity.  In particular the kernel is
finite and passing to the logarithmic image does not change integral rank.
-/

namespace Submission.CField.HQuotie

open IsDedekindDomain NumberField Representation
open Submission.NumberTheory.Milne
open Submission.CField.Ideles
open Submission.CField.ICohomo
open Submission.CField.NIndex

noncomputable section

universe u

variable {K L : Type u} [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- If all logarithmic coordinates vanish, the corresponding field element
has valuation one at every finite prime. -/
theorem upper_log_valuation
    (S : Finset (NumberFieldPlace K))
    (x : Additive (unitsAtPlaces (K := K) (L := L) S))
    (hlog : upperUnitLog (K := K) (L := L) S x = 0)
    (Q : FinitePrime L) :
    Q.valuation L (((Additive.toMul x :
      unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L) = 1 := by
  let xL : L := (((Additive.toMul x :
    unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L)
  by_cases hQ : Q ∈ primesAbovePlaces (K := K) (L := L) S
  · let P : FinitePrime K := Q.under (NumberField.RingOfIntegers K)
    letI : Fact (FinitePlace.mk P).val.IsNontrivial :=
      ⟨absolute_value_nontrivial P⟩
    letI : IsUltrametricDist (FinitePlace.mk P).val.Completion :=
      placeUltrametricDist P
    let vS : S := ⟨Sum.inl P, hQ⟩
    let Qabove : PrimesAboveBase (K := K) (L := L) P := ⟨Q, rfl⟩
    let qFactor : UpperPrimeFactors (K := K) (L := L) P :=
      (upperAboveBase
        (K := K) (L := L) P).symm Qabove
    let z : CompletionPlacesAbove (L := L) (FinitePlace.mk P).val :=
      (placesAboveFactors
        (K := K) (L := L) P).symm qFactor
    let t : upperPlacesAt (K := K) (L := L) S := ⟨vS, z⟩
    have hcoord := congrFun hlog t
    have hzlog : Real.log (z.1 xL) = 0 := by
      simpa [t, vS, P, xL, upper_unit_log] using hcoord
    have hzOne : z.1 xL = 1 :=
      Real.eq_one_of_pos_of_log_eq_zero
        (z.1.pos ((Additive.toMul x :
          unitsAtPlaces (K := K) (L := L) S) : Lˣ).ne_zero) hzlog
    have hzcenter :
        (placeAboveBase
          (K := K) (L := L) P z).1 = Q := by
      have hfac := (placesAboveFactors
        (K := K) (L := L) P).apply_symm_apply qFactor
      have hcenterSubtype :
          placeAboveBase
              (K := K) (L := L) P z = Qabove := by
        apply (upperAboveBase
          (K := K) (L := L) P).symm.injective
        exact hfac
      exact congrArg Subtype.val hcenterSubtype
    have hzcenter' :
        nonarchimedeanHeightSpectrum z.1
          (absolute_extension_nontrivial (FinitePlace.mk P).val z)
          (absolute_extension_nonarchimedean (FinitePlace.mk P).val z) = Q := by
      simpa only [placeAboveBase] using hzcenter
    have hequiv := place_centered_prime z.1
      (absolute_extension_nontrivial (FinitePlace.mk P).val z)
      (absolute_extension_nonarchimedean (FinitePlace.mk P).val z)
    rw [hzcenter'] at hequiv
    have hactual : (FinitePlace.mk Q).1 xL = 1 :=
      hequiv.eq_one_iff.mp hzOne
    have hnorm : ‖FinitePlace.embedding Q xL‖ = 1 := by
      simpa only [FinitePlace.mk_apply] using hactual
    rw [FinitePlace.norm_embedding'] at hnorm
    have h' :
        WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero Q)
            (Q.valuation L xL) = 1 := by
      exact_mod_cast hnorm
    exact (WithZeroMulInt.toNNReal_eq_one_iff
      (Q.valuation L xL)
      (HeightOneSpectrum.absNorm_ne_zero Q)
      (ne_of_gt (HeightOneSpectrum.one_lt_absNorm_nnreal Q))).mp h'
  · exact (Additive.toMul x).property Q hQ

omit [FiniteDimensional K L] [IsGalois K L] in
/-- If all logarithmic coordinates vanish and `S` contains the infinite
places, the corresponding field element has absolute value one at every
infinite place of `L`. -/
theorem upper_log_infinite
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (x : Additive (unitsAtPlaces (K := K) (L := L) S))
    (hlog : upperUnitLog (K := K) (L := L) S x = 0)
    (w : InfinitePlace L) :
    w (((Additive.toMul x :
      unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L) = 1 := by
  let v : InfinitePlace K := w.comap (algebraMap K L)
  let vS : S := ⟨Sum.inr v, hSinf v⟩
  let z : CompletionPlacesAbove (L := L) v.1 :=
    ⟨w.1, infinite_lies_comap v w rfl⟩
  let t : upperPlacesAt (K := K) (L := L) S := ⟨vS, z⟩
  have hcoord := congrFun hlog t
  have hwlog : Real.log
      (w (((Additive.toMul x :
        unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L)) = 0 := by
    simpa [t, z, vS, v, upper_unit_log] using hcoord
  exact Real.eq_one_of_pos_of_log_eq_zero
    (w.1.pos ((Additive.toMul x :
      unitsAtPlaces (K := K) (L := L) S) : Lˣ).ne_zero) hwlog

/-- The kernel of Milne's logarithmic map consists exactly of the roots of
unity in the `T`-unit group. -/
theorem upper_log_torsion
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S)
    (x : Additive (unitsAtPlaces (K := K) (L := L) S)) :
    x ∈ (upperUnitLog (K := K) (L := L) S).ker ↔
      Additive.toMul x ∈ CommGroup.torsion
        (unitsAtPlaces (K := K) (L := L) S) := by
  constructor
  · intro hlog
    let xL : L := (((Additive.toMul x :
      unitsAtPlaces (K := K) (L := L) S) : Lˣ) : L)
    have hxIntegral : IsIntegral ℤ xL := by
      apply (IsIntegralClosure.isIntegral_iff
        (A := NumberField.RingOfIntegers L)).mpr
      exact IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
        L xL fun Q => by
          rw [upper_log_valuation
            (K := K) (L := L) S x hlog Q]
    have hxEmbedding : ∀ phi : L →+* ℂ, ‖phi xL‖ = 1 := by
      intro phi
      exact upper_log_infinite
        (K := K) (L := L) S hSinf x hlog (InfinitePlace.mk phi)
    obtain ⟨n, hn, hxpow⟩ :=
      integral_all_conjugates
        L hxIntegral hxEmbedding
    rw [CommGroup.mem_torsion]
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact hxpow
  · intro hx
    rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one] at hx
    obtain ⟨n, hn, hxpow⟩ := hx
    have hxadd : n • x = 0 := by
      apply Additive.toMul.injective
      simpa using hxpow
    have hmap : n • upperUnitLog (K := K) (L := L) S x = 0 := by
      rw [← map_nsmul, hxadd, map_zero]
    funext t
    have ht := congrFun hmap t
    have ht' : n • upperUnitLog (K := K) (L := L) S x t = 0 := by
      simpa using ht
    rw [nsmul_eq_mul] at ht'
    exact (mul_eq_zero.mp ht').resolve_left (Nat.cast_ne_zero.mpr hn.ne')

/-- The kernel of the logarithmic map is finite. -/
theorem upper_log_ker
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Finite (upperUnitLog (K := K) (L := L) S).ker := by
  letI : Module.Finite ℤ
      (Additive (unitsAtPlaces (K := K) (L := L) S)) :=
    units_places_module (K := K) (L := L) S
  letI : Module.Finite ℤ
      (upperUnitLog (K := K) (L := L) S).ker := inferInstance
  letI : AddGroup.FG
      (upperUnitLog (K := K) (L := L) S).ker :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  apply AddCommGroup.finite_of_fg_torsion
    (upperUnitLog (K := K) (L := L) S).ker
  intro x
  rw [isOfFinAddOrder_iff_nsmul_eq_zero]
  have hx := (upper_log_torsion
    (K := K) (L := L) S hSinf x.1).mp x.2
  rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one] at hx
  obtain ⟨n, hn, hxpow⟩ := hx
  refine ⟨n, hn, ?_⟩
  apply Subtype.ext
  apply Additive.toMul.injective
  simpa using hxpow

/-- Quotienting the `T`-units by the finite kernel does not change their
integral rank, so the logarithmic image has the expected `T`-unit rank. -/
theorem upper_lattice_finrank
    (S : Finset (NumberFieldPlace K))
    (hSinf : ∀ v : InfinitePlace K,
      (Sum.inr v : NumberFieldPlace K) ∈ S) :
    Module.finrank ℤ
        (upperLogLattice (K := K) (L := L) S) =
      NumberField.InfinitePlace.nrRealPlaces L +
        NumberField.InfinitePlace.nrComplexPlaces L +
          (primesAbovePlaces (K := K) (L := L) S).ncard - 1 := by
  let f := upperUnitLog (K := K) (L := L) S
  letI : Module.Finite ℤ
      (Additive (unitsAtPlaces (K := K) (L := L) S)) :=
    units_places_module (K := K) (L := L) S
  letI : Finite f.ker :=
    upper_log_ker (K := K) (L := L) S hSinf
  letI : Module.Finite ℤ f.ker := inferInstance
  have hker : Module.finrank ℤ f.ker = 0 := by
    apply Module.finrank_eq_zero_iff.mpr
    intro x
    refine ⟨(Nat.card f.ker : ℤ), ?_, ?_⟩
    · exact Int.ofNat_ne_zero.mpr Nat.card_pos.ne'
    · simpa only [Nat.cast_smul_eq_nsmul] using
        (card_nsmul_eq_zero' (G := f.ker) (x := x))
  have hrank := Submodule.finrank_quotient_add_finrank f.ker
  rw [LinearEquiv.finrank_eq f.quotKerEquivRange, hker, add_zero] at hrank
  change Module.finrank ℤ f.range = _
  rw [hrank]
  exact units_rank L
    (primesAbovePlaces (K := K) (L := L) S)
    (primes_above_places (K := K) (L := L) S)

end

end Submission.CField.HQuotie

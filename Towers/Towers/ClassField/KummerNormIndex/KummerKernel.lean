import Towers.ClassField.KummerNormIndex.KummerBridge
import Towers.ClassField.KummerNormIndex.LocalTarget

open scoped IsMulCommutative

/-!
# The Kummer kernel in Lemma VII.6.9

This file identifies the kernel of the local map in Lemma VII.6.9 with the
`S`-units which become `p`th powers in `L`, using Lemma VII.6.3.  It also
computes the order of `Gal(M/L)` from the Frobenius basis selected in Lemma
VII.6.2.
-/

namespace Towers.CField.KNIndex

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- Map an `S`-unit into the unit group of an extension field. -/
noncomputable def sUnitsHom
    (K L : Type u) [Field K] [Field L] [NumberField K]
    [Algebra K L] (S : Finset (NumberFieldPlace K)) :
    ArithmeticSUnits K (finitePrimePart K S) →* Lˣ :=
  (Units.map (algebraMap K L)).comp
    (Set.unit (finitePrimePart K S) K).subtype

/-- The subgroup of `S`-units which become `p`th powers in `L`. -/
def extensionPowerSubgroup
    (K L : Type u) [Field K] [Field L] [NumberField K]
    [Algebra K L] (p : ℕ) (S : Finset (NumberFieldPlace K)) :
    Subgroup (ArithmeticSUnits K (finitePrimePart K S)) :=
  (pthPowerSubgroup p Lˣ).comap
    (sUnitsHom K L S)

theorem extension_power_subgroup
    (K L : Type u) [Field K] [Field L] [NumberField K]
    [Algebra K L] (p : ℕ) (hp : 0 < p)
    (S : Finset (NumberFieldPlace K))
    (a : ArithmeticSUnits K (finitePrimePart K S)) :
    a ∈ extensionPowerSubgroup K L p S ↔
      PthPowerExtension K L p (a : Kˣ) := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨((y : Lˣ) : L), ?_⟩
    exact congrArg Units.val hy
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro h
      have ha0 : algebraMap K L (((a : Kˣ) : K)) = 0 := by
        rw [← hy, h, zero_pow hp.ne']
      exact (map_ne_zero (algebraMap K L)).2 (Units.ne_zero (a : Kˣ)) ha0
    refine ⟨Units.mk0 y hy0, ?_⟩
    apply Units.ext
    exact hy

/-- For an `S`-unit at a prime outside `S`, membership in the local
integer-unit power subgroup is equivalent to being a power in the completed
field. -/
theorem local_unit_power
    (p : ℕ) (hp : 0 < p)
    (K : Type u) [Field K] [NumberField K]
    (S : Finset (NumberFieldPlace K))
    (T : Finset (FinitePrime K))
    (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
      (Sum.inl P : NumberFieldPlace K) ∉ S)
    (a : ArithmeticSUnits K (finitePrimePart K S)) (P : T) :
    sUnitHom K S T hDisjoint P a ∈
        pthPowerSubgroup p (P.1.adicCompletionIntegers K)ˣ ↔
      PthPowerCompletion K p (a : Kˣ) P.1 := by
  let C := P.1.adicCompletion K
  let B := P.1.adicCompletionIntegers K
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(((y : Bˣ) : B) : C), ?_⟩
    have hy' := congrArg (fun z : Bˣ ↦ (((z : B) : C))) hy
    exact hy'
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro h
      have ha0 : algebraMap K C (((a : Kˣ) : K)) = 0 := by
        rw [← hy, h, zero_pow hp.ne']
      exact (map_ne_zero (algebraMap K C)).2
        (Units.ne_zero (a : Kˣ)) ha0
    have haVal : Valued.v
        (algebraMap K C (((a : Kˣ) : K))) = 1 := by
      change Valued.v
        (FinitePlace.embedding P.1 (((a : Kˣ) : K))) = 1
      rw [FinitePlace.embedding_apply,
        P.1.valuedAdicCompletion_eq_valuation']
      exact a.property P.1 (hDisjoint P.1 P.2)
    have hyVal : Valued.v y = 1 := by
      apply (pow_eq_one_iff_left hp.ne').mp
      rw [← map_pow, hy, haVal]
    let yB : B := ⟨y, hyVal.le⟩
    have hyUnit : IsUnit yB := by
      rw [IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      exact hyVal
    let yu : Bˣ := hyUnit.unit
    refine ⟨yu, ?_⟩
    apply Units.ext
    apply Subtype.ext
    change (y : C) ^ p = algebraMap K C (((a : Kˣ) : K))
    simpa only [yu, yB, hyUnit.unit_spec] using hy

set_option maxHeartbeats 4000000 in
-- Identifying the kernel combines the global Kummer criterion with dependent
-- finite-completion power tests at every selected prime.
set_option synthInstance.maxHeartbeats 1000000 in
/-- Lemma VII.6.3 identifies the kernel of the obvious local map with the
subgroup of `S`-units which become `p`th powers in `L`. -/
theorem obvious_ker_extension
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [IsGalois L M] [IsAbelianGalois K M]
    (hroots : (primitiveRoots p K).Nonempty)
    (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
    (S : Finset (NumberFieldPlace K))
    (hunramified : ∀ Q : FinitePrime M,
      (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
        Algebra.IsUnramifiedAt (OK K) Q.asIdeal)
    (hcontains : ContainsPthRoots K M p S)
    (T : Finset (FinitePrime K))
    (hDisjoint : ∀ P : FinitePrime K, P ∈ T →
      (Sum.inl P : NumberFieldPlace K) ∉ S)
    (hT : FrobeniusBasis
      (K := K) (L := L) (M := M) p hexponent S T) :
    (obviousMap K p S T hDisjoint).ker =
      extensionPowerSubgroup K L p S := by
  have hdetect := kummerBridgeStatement p hp K L M hroots hexponent S
    hunramified hcontains T hT
  ext a
  rw [extension_power_subgroup K L p hp.pos S a]
  rw [hdetect a]
  constructor
  · intro ha P hPT
    have ha' := congrFun (show obviousMap K p S T hDisjoint a = 1 by
      exact ha) ⟨P, hPT⟩
    rw [obviousMap_apply, Pi.one_apply] at ha'
    have haPower :
        sUnitHom K S T hDisjoint ⟨P, hPT⟩ a ∈
          pthPowerSubgroup p (P.adicCompletionIntegers K)ˣ :=
      (QuotientGroup.eq_one_iff _).mp ha'
    exact (local_unit_power p hp.pos K S T hDisjoint
      a ⟨P, hPT⟩).mp haPower
  · intro ha
    change obviousMap K p S T hDisjoint a = 1
    funext P
    rw [obviousMap_apply, Pi.one_apply]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (local_unit_power p hp.pos K S T hDisjoint
      a P).mpr (ha P.1 P.2)

/-- The Frobenius basis in Lemma VII.6.2 gives
`|Gal(M/L)| = p ^ |T|`. -/
theorem galois_card_eq
    (p : ℕ) (K L M : Type u)
    [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M]
    [IsGalois L M] [IsAbelianGalois K M]
    (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
    (S : Finset (NumberFieldPlace K)) (T : Finset (FinitePrime K))
    (hT : FrobeniusBasis
      (K := K) (L := L) (M := M) p hexponent S T) :
    Nat.card Gal(M/L) = p ^ T.card := by
  letI : IsMulCommutative Gal(M/L) :=
    gal_ml_commutative (K := K) (L := L) (M := M)
  letI : CommGroup Gal(M/L) := inferInstance
  letI : Module (ZMod p) (Additive Gal(M/L)) :=
    exponentPModule p (gal_ml_pow
      (K := K) (L := L) (M := M) p hexponent)
  rcases hT with ⟨i, fi, indexPrime, _w, b, hindex, _⟩
  letI : Fintype i := fi
  let eIndex : i ≃ T := Equiv.ofBijective indexPrime hindex
  calc
    Nat.card Gal(M/L) = Nat.card (Additive Gal(M/L)) := rfl
    _ = Nat.card (i → ZMod p) := Nat.card_congr b.equivFun.toEquiv
    _ = Nat.card (ZMod p) ^ Nat.card i := Nat.card_fun
    _ = p ^ Fintype.card i := by simp
    _ = p ^ Fintype.card T := by rw [Fintype.card_congr eIndex]
    _ = p ^ T.card := by simp

end

end Towers.CField.KNIndex

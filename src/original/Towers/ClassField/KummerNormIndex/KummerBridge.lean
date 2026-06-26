import Towers.ClassField.KummerNormIndex.KummerGlobal
import Towers.ClassField.KummerNormIndex.KummerLocal

/-! # Assembly of the Kummer/local bridge in Lemma VII.6.3 -/

namespace Towers.CField.KNIndex

open IsDedekindDomain NumberField
open Towers.NumberTheory.Milne
open Towers.CField.Ideles
open Towers.CField.NIndex

noncomputable section

universe u

private abbrev OK (F : Type u) [Field F] [NumberField F] :=
  NumberField.RingOfIntegers F

set_option synthInstance.maxHeartbeats 500000 in
-- The bridge specializes both the global fixed-field and finite-completion
-- criteria in the full Kummer tower.
set_option maxHeartbeats 3000000 in
/-- The actual fixed-field and local-completion comparison used in Lemma
VII.6.3. -/
theorem kummerFixedBridge :
    KummerFixedBridge.{u} := by
  intro p hp K L M
    _ _ _
    _ _ _
    _ _ _
    _
    _ _
    _ _
    hroot hexponent S hunramified
    T i fi indexPrime w hdisjoint hunder hcompat hfrobNe a z hzpow
  letI : Fintype i := fi
  constructor
  · exact pth_gal_fixed
      p hp K L M hroot (a : Kˣ) z hzpow
  · intro j
    have hwNotS :
        (Sum.inl ((w j).under (OK K)) : NumberFieldPlace K) ∉ S := by
      rw [hunder j]
      exact hdisjoint (indexPrime j : FinitePrime K) (indexPrime j).property
    exact pth_frobenius_fixed
      p hp K L M hroot hexponent
      (indexPrime j : FinitePrime K) (w j) (hunder j)
      (hunramified (w j) hwNotS) (hcompat j) (hfrobNe j)
      (a : Kˣ) z hzpow

/-- **Lemma VII.6.3.**  For a set `T` carrying the Frobenius basis from
Lemma VII.6.2, an `S`-unit is a `p`th power in `L` exactly when it is a
`p`th power in every selected completion `K_v`. -/
theorem kummerBridgeStatement : (∀ (p : ℕ) (_hp : p.Prime)
      (K L M : Type u)
      [Field K] [Field L] [Field M]
      [NumberField K] [NumberField L] [NumberField M]
      [Algebra K L] [Algebra L M] [Algebra K M]
      [IsScalarTower K L M]
      [FiniteDimensional K L] [FiniteDimensional L M]
      [IsGalois L M] [IsAbelianGalois K M],
      (primitiveRoots p K).Nonempty →
      ∀ (hexponent : ∀ sigma : Gal(M/K), sigma ^ p = 1)
        (S : Finset (NumberFieldPlace K)),
        (∀ Q : FinitePrime M,
          (Sum.inl (Q.under (OK K)) : NumberFieldPlace K) ∉ S →
            Algebra.IsUnramifiedAt (OK K) Q.asIdeal) →
        ContainsPthRoots K M p S →
        ∀ T : Finset (FinitePrime K),
          FrobeniusBasis (K := K) (L := L) (M := M)
              p hexponent S T →
            PowerDetection K L p S T) :=
  part_statement_bridge kummerFixedBridge

end

end Towers.CField.KNIndex

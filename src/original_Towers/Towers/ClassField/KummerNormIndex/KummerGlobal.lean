import Towers.ClassField.KummerNormIndex.FinitePrimePart

/-! # The global fixed-field step in Lemma VII.6.3 -/

namespace Towers.CField.KNIndex

open NumberField

noncomputable section

universe u

/-- Over a field containing a primitive `p`th root of unity, if an element
upstairs and a nonzero element downstairs have the same `p`th power, then
the upstairs element already comes from downstairs. -/
theorem algebra_pow
    (p : ℕ) [NeZero p]
    {F E : Type u} [Field F] [Field E] [Algebra F E]
    (zeta : F) (hzeta : IsPrimitiveRoot zeta p)
    (x : E) (b : F) (hb : b ≠ 0)
    (hpow : x ^ p = algebraMap F E (b ^ p)) :
    ∃ c : F, algebraMap F E c = x := by
  have hbE : algebraMap F E b ≠ 0 :=
    (map_ne_zero (algebraMap F E)).2 hb
  have hratio : (x / algebraMap F E b) ^ p = 1 := by
    rw [div_pow, hpow, map_pow]
    exact div_self (pow_ne_zero p hbE)
  have hzetaE : IsPrimitiveRoot (algebraMap F E zeta) p :=
    hzeta.map_of_injective (algebraMap F E).injective
  obtain ⟨n, _hnlt, hn⟩ := hzetaE.eq_pow_of_pow_eq_one hratio
  refine ⟨zeta ^ n * b, ?_⟩
  calc
    algebraMap F E (zeta ^ n * b) =
        (algebraMap F E zeta) ^ n * algebraMap F E b := by
      rw [map_mul, map_pow]
    _ = (x / algebraMap F E b) * algebraMap F E b := by rw [hn]
    _ = x := div_mul_cancel₀ x hbE

/-- If the base contains the `p`th roots of unity, a chosen `p`th root in a
Galois overfield comes from the intermediate field exactly when the relative
Galois group fixes it. -/
theorem pth_gal_fixed
    (p : ℕ) (hp : p.Prime)
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M]
    [FiniteDimensional L M] [IsGalois L M]
    (hroot : (primitiveRoots p K).Nonempty)
    (a : Kˣ) (z : M)
    (hzpow : z ^ p = algebraMap K M (a : K)) :
    PthPowerExtension K L p a ↔
      ∀ sigma : Gal(M/L), sigma z = z := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  constructor
  · rintro ⟨b, hbpow⟩
    have hbne : b ≠ 0 := by
      intro hb
      subst b
      have ha_ne : algebraMap K L (a : K) ≠ 0 :=
        (map_ne_zero (algebraMap K L)).2 (Units.ne_zero a)
      exact ha_ne (by simpa [hp.ne_zero] using hbpow.symm)
    have hbMne : algebraMap L M b ≠ 0 :=
      (map_ne_zero (algebraMap L M)).2 hbne
    obtain ⟨zeta, hzeta_mem⟩ := hroot
    have hzetaK : IsPrimitiveRoot zeta p :=
      isPrimitiveRoot_of_mem_primitiveRoots hzeta_mem
    have hzetaM : IsPrimitiveRoot (algebraMap K M zeta) p :=
      hzetaK.map_of_injective (algebraMap K M).injective
    have hratio : (z / algebraMap L M b) ^ p = 1 := by
      rw [div_pow, hzpow, ← map_pow, hbpow]
      rw [IsScalarTower.algebraMap_apply K L M]
      exact div_self ((map_ne_zero (algebraMap L M)).2
        ((map_ne_zero (algebraMap K L)).2 (Units.ne_zero a)))
    obtain ⟨n, _hnlt, hn⟩ := hzetaM.eq_pow_of_pow_eq_one hratio
    let c : L := (algebraMap K L zeta) ^ n * b
    have hcz : algebraMap L M c = z := by
      calc
        algebraMap L M c =
            (algebraMap L M (algebraMap K L zeta)) ^ n *
              algebraMap L M b := by
          rw [map_mul, map_pow]
        _ = (algebraMap K M zeta) ^ n * algebraMap L M b := by
          rw [IsScalarTower.algebraMap_apply K L M]
        _ = (z / algebraMap L M b) * algebraMap L M b := by
          rw [hn]
        _ = z := div_mul_cancel₀ z hbMne
    intro sigma
    rw [← hcz]
    exact sigma.commutes c
  · intro hfixed
    obtain ⟨b, hbz⟩ :=
      (IsGalois.mem_range_algebraMap_iff_fixed
        (F := L) (E := M) z).2 hfixed
    refine ⟨b, ?_⟩
    apply (algebraMap L M).injective
    calc
      algebraMap L M (b ^ p) = z ^ p := by rw [map_pow, hbz]
      _ = algebraMap K M (a : K) := hzpow
      _ = algebraMap L M (algebraMap K L (a : K)) :=
        IsScalarTower.algebraMap_apply K L M (a : K)

end

end Towers.CField.KNIndex

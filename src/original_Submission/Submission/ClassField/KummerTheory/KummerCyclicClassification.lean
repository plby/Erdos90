import Submission.ClassField.KummerTheory.KummerRadicalExtension

/-!
# Classification of cyclic radical presentations

This file proves the character-theoretic core of Proposition VII.A.2.  Two
radical generators of the same degree-`n` extension differ by a coprime power
and an `n`th-power scalar from the base field.  Conversely, such a relation
between the radicands forces the generated intermediate fields to coincide.
-/

namespace Submission.CField.KTheory

open Module Polynomial IntermediateField

noncomputable section

universe u

variable {K L Ω : Type u} [Field K] [Field L] [Field Ω]
  [Algebra K L] [Algebra K Ω]

/-- The hard direction of Proposition A.2, formulated after identifying the
two cyclic extensions.  If two `n`th radicals generate the same degree-`n`
extension, their radicands differ by a coprime power and an `n`th power.

The proof compares the two faithful characters of a generator of the Galois
group and descends their quotient through the fixed field. -/
theorem relation_two_generators
    [FiniteDimensional K L] {n : ℕ} (hn : 0 < n)
    {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {a b : Kˣ} {α β : L}
    (hdim : finrank K L = n)
    (ha : α ^ n = algebraMap K L (a : K))
    (hb : β ^ n = algebraMap K L (b : K))
    (hα : K⟮α⟯ = ⊤) (hβ : K⟮β⟯ = ⊤) :
    ∃ r < n, r.Coprime n ∧ ∃ c : Kˣ,
      (a : K) = (b : K) ^ r * (c : K) ^ n := by
  have hroots : (primitiveRoots (finrank K L) K).Nonempty := by
    refine ⟨ζ, ?_⟩
    rw [mem_primitiveRoots finrank_pos, hdim]
    exact hζ
  have hbfin : β ^ finrank K L = algebraMap K L (b : K) := by
    rw [hdim]
    exact hb
  have hcyclic := radical_generator_cyclic K L hroots hbfin hβ
  letI : IsGalois K L := hcyclic.1
  letI : IsCyclic Gal(L/K) := hcyclic.2
  letI : NeZero n := ⟨hn.ne'⟩
  have hirr : Irreducible (X ^ n - C (b : K)) := by
    simpa [hdim] using
      (irreducible_X_pow_sub_C_of_root_adjoin_eq_top hbfin hβ)
  letI : IsSplittingField K L (X ^ n - C (b : K)) := by
    simpa [hdim] using
      (isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hroots hbfin hβ)
  let hprim : (primitiveRoots n K).Nonempty :=
    ⟨ζ, (mem_primitiveRoots hn).2 hζ⟩
  let σ : Gal(L/K) :=
    (autEquivRootsOfUnity hprim hirr L).symm
      ⟨Units.mk0 ζ (hζ.ne_zero hn.ne'),
        (mem_rootsOfUnity' n _).2 hζ.pow_eq_one⟩
  have hσβ : σ β = algebraMap K L ζ * β := by
    simpa [σ, Algebra.smul_def] using
      (autEquivRootsOfUnity_smul hprim hirr L hb σ).symm
  have hαne : α ≠ 0 := by
    intro hzero
    have : algebraMap K L (a : K) = 0 := by rw [← ha, hzero, zero_pow hn.ne']
    exact (map_ne_zero (algebraMap K L)).2 a.ne_zero this
  have hratio_pow : (σ α / α) ^ n = 1 := by
    calc
      (σ α / α) ^ n = σ (α ^ n) / α ^ n := by rw [div_pow, map_pow]
      _ = algebraMap K L (a : K) / algebraMap K L (a : K) := by
        rw [ha, σ.commutes]
      _ = 1 := div_self ((map_ne_zero (algebraMap K L)).2 a.ne_zero)
  obtain ⟨r, hrlt, hr⟩ :=
    (hζ.map_of_injective (algebraMap K L).injective).eq_pow_of_pow_eq_one hratio_pow
  have hσα : σ α = algebraMap K L (ζ ^ r) * α := by
    apply (div_eq_iff hαne).mp
    simpa only [map_pow] using hr.symm
  have hζr : IsPrimitiveRoot (ζ ^ r) n := by
    refine ⟨?_, ?_⟩
    · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    intro d hd
    have hfixα : (σ ^ d) α = α := by
      let f : Module.End K L := σ.toLinearMap
      have heigen : f.HasEigenvector (ζ ^ r) α := by
        refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hαne⟩
        simpa [AlgEquiv.toLinearMap_apply, Algebra.smul_def] using hσα
      have heigenpow := heigen.pow_apply d
      change (σ.toLinearMap ^ d) α = (ζ ^ r) ^ d • α at heigenpow
      rw [← AlgEquiv.pow_toLinearMap] at heigenpow
      simpa [hd] using heigenpow
    have hσpow : σ ^ d = 1 := by
      apply AlgEquiv.coe_algHom_injective
      have hadj : Algebra.adjoin K {α} = ⊤ := by
        rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
          (Algebra.IsAlgebraic.isAlgebraic α), hα]
        rfl
      apply AlgHom.ext_of_adjoin_eq_top hadj
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      simpa using hfixα
    have himage :
        (autEquivRootsOfUnity hprim hirr L) (σ ^ d) =
          (⟨Units.mk0 ζ (hζ.ne_zero hn.ne'),
            (mem_rootsOfUnity' n _).2 hζ.pow_eq_one⟩ :
            rootsOfUnity n K) ^ d := by
      rw [map_pow, MulEquiv.apply_symm_apply]
    rw [hσpow, map_one] at himage
    apply hζ.dvd_of_pow_eq_one d
    exact Units.ext_iff.mp (Subtype.ext_iff.mp himage.symm)
  have hcoprime : r.Coprime n :=
    (hζ.pow_iff_coprime hn r).mp hζr
  have hσβr : σ (β ^ r) = algebraMap K L (ζ ^ r) * β ^ r := by
    rw [map_pow, hσβ, mul_pow, ← map_pow]
  let x : L := α / β ^ r
  have hβne : β ≠ 0 := by
    intro hzero
    have : algebraMap K L (b : K) = 0 := by rw [← hb, hzero, zero_pow hn.ne']
    exact (map_ne_zero (algebraMap K L)).2 b.ne_zero this
  have hσx : σ x = x := by
    dsimp [x]
    rw [map_div₀ σ, hσα, hσβr]
    exact mul_div_mul_left _ _
      ((map_ne_zero (algebraMap K L)).2 (pow_ne_zero r (hζ.ne_zero hn.ne')))
  have hfixed : ∀ τ : Gal(L/K), τ x = x := by
    intro τ
    obtain ⟨m, hm_lt, hm⟩ := hζ.eq_pow_of_pow_eq_one
      (show (((autEquivRootsOfUnity hprim hirr L τ : rootsOfUnity n K) : Kˣ) : K) ^ n = 1
        from congrArg Units.val (autEquivRootsOfUnity hprim hirr L τ).2)
    have hτ : τ = σ ^ m := by
      apply (autEquivRootsOfUnity hprim hirr L).injective
      rw [map_pow, MulEquiv.apply_symm_apply]
      ext
      simpa using hm.symm
    rw [hτ]
    have hxne : x ≠ 0 := div_ne_zero hαne (pow_ne_zero r hβne)
    let f : Module.End K L := σ.toLinearMap
    have heigenx : f.HasEigenvector 1 x := by
      refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hxne⟩
      simpa [AlgEquiv.toLinearMap_apply] using hσx
    have heigenpow := heigenx.pow_apply m
    change (σ.toLinearMap ^ m) x = (1 : K) ^ m • x at heigenpow
    rw [← AlgEquiv.pow_toLinearMap] at heigenpow
    simpa using heigenpow
  obtain ⟨c0, hc0⟩ := IntermediateField.mem_bot.mp
    ((IsGalois.mem_bot_iff_fixed x).2 hfixed)
  have hc0ne : c0 ≠ 0 := by
    intro hc
    have hxzero : x = 0 := by simpa [hc] using hc0.symm
    apply hαne
    have : α / β ^ r = 0 := by simpa [x] using hxzero
    exact (div_eq_zero_iff).mp this |>.resolve_right (pow_ne_zero r hβne)
  let c : Kˣ := Units.mk0 c0 hc0ne
  refine ⟨r, hrlt, hcoprime, c, ?_⟩
  have hαform : α = algebraMap K L c0 * β ^ r := by
    apply (div_eq_iff (pow_ne_zero r hβne)).mp
    simpa [x] using hc0.symm
  apply (algebraMap K L).injective
  rw [← ha, hαform, mul_pow, ← pow_mul, mul_comm r n, pow_mul, hb,
    ← map_pow, ← map_pow, map_mul]
  exact mul_comm _ _

/-- The reverse implication in Proposition A.2.  A coprime-power relation is
more than is needed for this direction: if the radicands differ by a power
and an `n`th power, the first radical field embeds in the second; equality of
their degrees then makes the inclusion an equality. -/
theorem fields_radicand_relation
    {n r : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {a b c : Kˣ} {α β : Ω}
    (ha : α ^ n = algebraMap K Ω (a : K))
    (hb : β ^ n = algebraMap K Ω (b : K))
    (hab : (a : K) = (b : K) ^ r * (c : K) ^ n)
    (hdegα : finrank K K⟮α⟯ = n)
    (hdegβ : finrank K K⟮β⟯ = n) :
    K⟮α⟯ = K⟮β⟯ := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hαne : α ≠ 0 := by
    intro hzero
    have : algebraMap K Ω (a : K) = 0 := by rw [← ha, hzero, zero_pow hn.ne']
    exact (map_ne_zero (algebraMap K Ω)).2 a.ne_zero this
  have hβne : β ≠ 0 := by
    intro hzero
    have : algebraMap K Ω (b : K) = 0 := by rw [← hb, hzero, zero_pow hn.ne']
    exact (map_ne_zero (algebraMap K Ω)).2 b.ne_zero this
  let y : Ω := algebraMap K Ω (c : K) * β ^ r
  have hyne : y ≠ 0 :=
    mul_ne_zero ((map_ne_zero (algebraMap K Ω)).2 c.ne_zero) (pow_ne_zero r hβne)
  have hypow : y ^ n = algebraMap K Ω (a : K) := by
    dsimp [y]
    rw [mul_pow, ← pow_mul, mul_comm r n, pow_mul, hb,
      ← map_pow, ← map_pow, ← map_mul]
    rw [hab, mul_comm]
  have hratio : (α / y) ^ n = 1 := by
    rw [div_pow, ha, hypow, div_self]
    exact (map_ne_zero (algebraMap K Ω)).2 a.ne_zero
  obtain ⟨i, hi, hroot⟩ :=
    (hζ.map_of_injective (algebraMap K Ω).injective).eq_pow_of_pow_eq_one hratio
  have hαform : α = algebraMap K Ω (ζ ^ i) * y := by
    apply (div_eq_iff hyne).mp
    simpa only [map_pow] using hroot.symm
  have hαmem : α ∈ K⟮β⟯ := by
    rw [hαform]
    exact mul_mem (IntermediateField.algebraMap_mem K⟮β⟯ (ζ ^ i))
      (mul_mem (IntermediateField.algebraMap_mem K⟮β⟯ (c : K))
        (pow_mem (IntermediateField.mem_adjoin_simple_self K β) r))
  have hle : K⟮α⟯ ≤ K⟮β⟯ := adjoin_simple_le_iff.mpr hαmem
  have hβint : IsIntegral K β := by
    refine ⟨X ^ n - C (b : K), monic_X_pow_sub_C (b : K) hn.ne', ?_⟩
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hb, sub_self]
  letI : FiniteDimensional K K⟮β⟯ :=
    IntermediateField.adjoin.finiteDimensional hβint
  exact IntermediateField.eq_of_le_of_finrank_eq hle (hdegα.trans hdegβ.symm)

/-- **Proposition VII.A.2.**  Two degree-`n` cyclic radical extensions in a
common overfield are equal exactly when their radicands differ by a power
coprime to `n` and an `n`th power in the base field.

The exponent is chosen in the canonical range `0 ≤ r < n`; this is the
natural-number version of the integer exponent in the book. -/
theorem cyclic_radical_extensions
    {n : ℕ} (hn : 0 < n) {ζ : K} (hζ : IsPrimitiveRoot ζ n)
    {a b : Kˣ} {α β : Ω}
    (ha : α ^ n = algebraMap K Ω (a : K))
    (hb : β ^ n = algebraMap K Ω (b : K))
    (hdegα : finrank K K⟮α⟯ = n)
    (hdegβ : finrank K K⟮β⟯ = n) :
    K⟮α⟯ = K⟮β⟯ ↔
      ∃ r < n, r.Coprime n ∧ ∃ c : Kˣ,
        (a : K) = (b : K) ^ r * (c : K) ^ n := by
  constructor
  · intro heq
    let F : IntermediateField K Ω := K⟮β⟯
    have hβint : IsIntegral K β := by
      refine ⟨X ^ n - C (b : K), monic_X_pow_sub_C (b : K) hn.ne', ?_⟩
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hb, sub_self]
    letI : FiniteDimensional K F :=
      IntermediateField.adjoin.finiteDimensional hβint
    let αF : F := ⟨α, by
      change α ∈ K⟮β⟯
      rw [← heq]
      exact IntermediateField.mem_adjoin_simple_self K α⟩
    let βF : F := ⟨β, IntermediateField.mem_adjoin_simple_self K β⟩
    have haF : αF ^ n = algebraMap K F (a : K) := by
      apply Subtype.ext
      exact ha
    have hbF : βF ^ n = algebraMap K F (b : K) := by
      apply Subtype.ext
      exact hb
    have hgenα : K⟮αF⟯ = ⊤ := by
      apply IntermediateField.map_injective F.val
      rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map]
      simp only [Set.image_singleton, αF]
      rw [IntermediateField.fieldRange_val]
      exact heq
    have hgenβ : K⟮βF⟯ = ⊤ := by
      apply IntermediateField.map_injective F.val
      rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map]
      simp only [Set.image_singleton, βF]
      rw [IntermediateField.fieldRange_val]
      rfl
    exact relation_two_generators hn hζ hdegβ
      haF hbF hgenα hgenβ
  · rintro ⟨r, hrlt, hrcoprime, c, hab⟩
    exact fields_radicand_relation hn hζ ha hb hab hdegα hdegβ

end

end Submission.CField.KTheory

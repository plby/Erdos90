import Towers.ClassField.NormLimitation.PrimeIndexSupergroup
import Towers.ClassField.NormLimitation.ReductionData
import Towers.ClassField.NormIndex.FiniteIdeleContinuity
import Towers.ClassField.KummerNormIndex.CoprimeExponent
import Towers.ClassField.KummerNormIndex.CyclotomicDegree
import Towers.ClassField.KummerNormIndex.NormExponent
import Mathlib.NumberTheory.Cyclotomic.Gal

/-!
# The prime-index reduction in Theorem VII.9.5

Once a prime-index supergroup `U₁` is realized as the range of an
idèle-class norm by Lemma 9.3, its defining extension is precisely the
overfield needed for the induction.  The preimage of `U` then has index
`U.index / p`, hence strictly smaller index.
-/

namespace Towers.CField.NLimita

open NumberField
open Towers.CField.LFTheory
open Towers.CField.Ideles
open Towers.CField.Recip
open Towers.CField.NIndex
open Towers.CField.KNIndex

noncomputable section

universe u

private abbrev CK (K : Type u) [Field K] [NumberField K] :=
  IdeleClassGroup (RingOfIntegers K) K

/-- If `f` admits a section up to the `m`th-power map, then it is
surjective modulo every exponent-`p` subgroup when `m` and `p` are
coprime.  Consequently the pullback subgroup has the same index. -/
private theorem comap_coprime_section
    {C D : Type*} [CommGroup C] [CommGroup D]
    (U : Subgroup C) (f : D →* C) (i : C →* D)
    (p m : ℕ) (hindex : U.index = p)
    (hexponent : ∀ x : C ⧸ U, x ^ p = 1)
    (hcop : m.Coprime p)
    (hcomp : f.comp i = powMonoidHom m) :
    (U.comap f).index = p := by
  let qU := QuotientGroup.mk' U
  have hpow : Function.Surjective
      (powMonoidHom m : (C ⧸ U) →* (C ⧸ U)) :=
    (Towers.CField.KNIndex.bijective_coprime_exponent
      hcop hexponent).2
  have hsurj : Function.Surjective (qU.comp f) := by
    intro x
    obtain ⟨y, hy⟩ := hpow x
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective U y
    refine ⟨i c, ?_⟩
    calc
      qU (f (i c)) = qU (c ^ m) := by
        rw [show f (i c) = c ^ m by
          exact DFunLike.congr_fun hcomp c]
      _ = (qU c) ^ m := map_pow qU c m
      _ = x := hy
  have hrange : f.range.map qU = ⊤ := by
    rw [MonoidHom.map_range, MonoidHom.range_eq_top]
    exact hsurj
  have hsup : U ⊔ f.range = ⊤ := by
    rw [← QuotientGroup.comap_map_mk' U f.range, hrange,
      Subgroup.comap_top]
  rw [U.index_comap f]
  calc
    U.relIndex f.range = U.relIndex (f.range ⊔ U) := by
      rw [Subgroup.relIndex_sup_right]
    _ = U.relIndex ⊤ := by rw [sup_comm, hsup]
    _ = U.index := Subgroup.relIndex_top_right U
    _ = p := hindex

/-- A divisor of `p - 1` is coprime to the prime `p`. -/
private theorem coprime_dvd_pred
    {m p : ℕ} (hp : p.Prime) (hm : m ∣ p - 1) : m.Coprime p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hpm
  have hppred : p ∣ p - 1 := hpm.trans hm
  have hpos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hle : p ≤ p - 1 := Nat.le_of_dvd hpos hppred
  omega

/-- The topological fact about the canonical idèle-class norm needed by
the induction in Theorem 9.5. -/
def CanonicalContinuityBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L],
    Continuous (canonicalIdeleNorm (K := K) (L := L))

/-- The underlying topological assertion before passage to idèle classes. -/
def NormContinuityBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L],
    Continuous (ideleNorm (K := K) (L := L))

/-- After the archimedean calculation, the sole remaining continuity input
is the norm on the finite restricted product. -/
def IdeleContinuityBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L],
    Continuous (finiteIdeleNorm (K := K) (L := L))

/-- Continuity of all finite-idèle norms supplies continuity of the full
idèle norm. -/
theorem idele_norm_continuity
    (h : IdeleContinuityBridge.{u}) :
    NormContinuityBridge.{u} := by
  intro K L _ _ _ _ _ _
  exact continuous_idele_norm
    (h K L)

/-- Continuity of the idèle norm descends through the quotient maps to
continuity of the idèle-class norm. -/
theorem canonical_norm_continuity
    (h : NormContinuityBridge.{u}) :
    CanonicalContinuityBridge.{u} := by
  intro K L _ _ _ _ _ _
  rw [← (QuotientGroup.isOpenQuotientMap_mk
    (N := principalIdeles (RingOfIntegers L) L)).continuous_comp_iff]
  have hcontinuous :=
    (QuotientGroup.continuous_mk
      (N := principalIdeles (RingOfIntegers K) K)).comp (h K L)
  convert hcontinuous using 1

/-- Thus the canonical idèle-class norm is continuous once the finite
restricted-product norm is. -/
theorem canonical_idele_continuity
    (h : IdeleContinuityBridge.{u}) :
    CanonicalContinuityBridge.{u} :=
  canonical_norm_continuity
    (idele_norm_continuity h)

/-- For a finite Galois extension, the canonical idèle-class norm is
continuous.  This is the case used in the prime-index induction, where the
extension supplied by Lemma 9.3 is finite abelian. -/
theorem continuous_idele_galois
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L] :
    Continuous (canonicalIdeleNorm (K := K) (L := L)) := by
  rw [← (QuotientGroup.isOpenQuotientMap_mk
    (N := principalIdeles (RingOfIntegers L) L)).continuous_comp_iff]
  have hidele : Continuous (ideleNorm (K := K) (L := L)) :=
    continuous_idele_norm
      (Towers.CField.NIndex.continuous_finite_norm
        (K := K) (L := L))
  have hcontinuous :=
    (QuotientGroup.continuous_mk
      (N := principalIdeles (RingOfIntegers K) K)).comp hidele
  convert hcontinuous using 1

/-- If a chosen prime-index supergroup is realized by Lemma 9.3, its norm
extension supplies reduction data with strictly smaller pullback index. -/
theorem reduction_data_index
    (h93 : ExistenceStatementInterface.{u})
    (p : ℕ) (K : Type u) [Field K] [NumberField K]
    (hp : p.Prime) (hroots : (primitiveRoots p K).Nonempty)
    (U U₁ : Subgroup (CK K))
    (hUopen : IsOpen (U : Set (CK K)))
    (hUfinite : U.FiniteIndex)
    (hUU₁ : U ≤ U₁) (hU₁index : U₁.index = p)
    (hexponent : ∀ q : CK K ⧸ U₁, q ^ p = 1) :
    Nonempty (ReductionData K U) := by
  letI : U.FiniteIndex := hUfinite
  have hU₁open : IsOpen (U₁ : Set (CK K)) :=
    Subgroup.isOpen_mono hUU₁ hUopen
  have hU₁finite : U₁.FiniteIndex := by
    constructor
    rw [hU₁index]
    exact hp.ne_zero
  obtain ⟨L, hL⟩ :=
    h93 p K hp hroots U₁ hU₁open hU₁finite hexponent
  let K' := L.1
  letI : NumberField K' := NumberField.of_module_finite K K'
  let f : CK K' →* CK K :=
    canonicalIdeleNorm (K := K) (L := K')
  have hfrange : f.range = U₁ := by
    change (canonicalIdeleNorm (K := K) (L := K')).range = U₁
    rw [← idele_class_range L, hL]
  have hfcontinuous : Continuous f :=
    continuous_idele_galois K K'
  refine ⟨
    { K' := K'
      fieldK' := inferInstance
      numberFieldK' := inferInstance
      algebraKK' := inferInstance
      finiteDimensionalKK' := inferInstance
      preimage_isOpen := ?_
      preimage_finiteIndex := ?_
      preimage_index_lt := ?_ }⟩
  · exact hUopen.preimage hfcontinuous
  · exact finiteIndex_comap f U
  · exact index_comap_prime
      f U U₁ hUU₁ hfrange p hp hU₁index

/-- The standard identity used when adjoining roots of unity: extend an
idèle class and then take its norm to obtain the extension-degree power.
This is isolated because its current implementation is being adjusted
together with the finite idèle extension map. -/
def NormExtensionBridge : Prop :=
  ∀ (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsGalois K L],
    let E := canonicalExtensionData (K := K) (L := L)
    (canonicalIdeleNorm (K := K) (L := L)).comp E.classMap =
      powMonoidHom (Module.finrank K L)

/-- The canonical idèle extension and norm maps satisfy the required power
identity. -/
theorem normExtensionBridge :
    NormExtensionBridge.{u} := by
  intro K L _ _ _ _ _ _ _
  exact canonical_comp_extension K L

/-- The two-stage reduction used in the source when the original field
does not yet contain the required root of unity.  First pass to the
`p`th cyclotomic field, then perform the prime-index reduction there. -/
structure CyclotomicReductionData
    (K : Type u) [Field K] [NumberField K]
    (U : Subgroup (CK K)) where
  K' : Type u
  fieldK' : Field K'
  numberFieldK' : NumberField K'
  algebraKK' : Algebra K K'
  finiteDimensionalKK' : FiniteDimensional K K'
  preimage_isOpen :
    letI : Field K' := fieldK'
    letI : NumberField K' := numberFieldK'
    letI : Algebra K K' := algebraKK'
    letI : FiniteDimensional K K' := finiteDimensionalKK'
    IsOpen (U.comap (canonicalIdeleNorm (K := K) (L := K')) :
      Set (CK K'))
  preimage_finiteIndex :
    letI : Field K' := fieldK'
    letI : NumberField K' := numberFieldK'
    letI : Algebra K K' := algebraKK'
    letI : FiniteDimensional K K' := finiteDimensionalKK'
    (U.comap (canonicalIdeleNorm (K := K) (L := K'))).FiniteIndex
  preimage_index_le :
    letI : Field K' := fieldK'
    letI : NumberField K' := numberFieldK'
    letI : Algebra K K' := algebraKK'
    letI : FiniteDimensional K K' := finiteDimensionalKK'
    (U.comap (canonicalIdeleNorm (K := K) (L := K'))).index ≤ U.index
  primeReduction :
    letI : Field K' := fieldK'
    letI : NumberField K' := numberFieldK'
    letI : Algebra K K' := algebraKK'
    letI : FiniteDimensional K K' := finiteDimensionalKK'
    ReductionData K'
      (U.comap (canonicalIdeleNorm (K := K) (L := K')))

set_option maxHeartbeats 2000000 in
-- The cyclotomic field carries several inferred number-field structures.
/-- Adjoining a primitive root of unity and applying Lemma 9.3 produces a
two-stage reduction whose final pullback has strictly smaller index. -/
theorem cyclotomicReductionData
    (h93 : ExistenceStatementInterface.{u})
    (hpower : NormExtensionBridge.{u})
    (K : Type u) [Field K] [NumberField K]
    (U : Subgroup (CK K))
    (hUopen : IsOpen (U : Set (CK K)))
    (hUfinite : U.FiniteIndex) (hUtop : U ≠ ⊤) :
    Nonempty (CyclotomicReductionData K U) := by
  letI : U.FiniteIndex := hUfinite
  obtain ⟨p, U₁, hp, hUU₁, hU₁index, hU₁exponent⟩ :=
    prime_index_supergroup U hUtop
  letI : Fact p.Prime := ⟨hp⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : NeZero (p : K) := ⟨Nat.cast_ne_zero.mpr hp.ne_zero⟩
  let K' := CyclotomicField p K
  letI : IsCyclotomicExtension {p} K K' :=
    CyclotomicField.isCyclotomicExtension p K
  letI : FiniteDimensional K K' :=
    IsCyclotomicExtension.finiteDimensional {p} K K'
  letI : NumberField K' :=
    IsCyclotomicExtension.numberField {p} K K'
  letI : IsGalois K K' :=
    IsCyclotomicExtension.isGalois {p} K K'
  let norm : CK K' →* CK K :=
    canonicalIdeleNorm (K := K) (L := K')
  let extension : CK K →* CK K' :=
    (canonicalExtensionData (K := K) (L := K')).classMap
  let m := Module.finrank K K'
  have hm : m ∣ p - 1 := by
    exact cyclotomic_dvd_pred hp K K'
  have hcop : m.Coprime p := coprime_dvd_pred hp hm
  have hcomp : norm.comp extension = powMonoidHom m := by
    exact hpower K K'
  let U' : Subgroup (CK K') := U.comap norm
  let U₁' : Subgroup (CK K') := U₁.comap norm
  have hU₁'index : U₁'.index = p := by
    exact comap_coprime_section
      U₁ norm extension p m hU₁index hU₁exponent hcop hcomp
  have hU'open : IsOpen (U' : Set (CK K')) := by
    exact hUopen.preimage
      (continuous_idele_galois K K')
  have hU'finite : U'.FiniteIndex := finiteIndex_comap norm U
  letI : U'.FiniteIndex := hU'finite
  have hU₁'finite : U₁'.FiniteIndex := by
    constructor
    rw [hU₁'index]
    exact hp.ne_zero
  have hUU₁' : U' ≤ U₁' := Subgroup.comap_mono hUU₁
  have hU₁'exponent : ∀ q : CK K' ⧸ U₁', q ^ p = 1 := by
    intro q
    calc
      q ^ p = q ^ U₁'.index :=
        congrArg (fun n ↦ q ^ n) hU₁'index.symm
      _ = 1 := pow_card_eq_one'
  have hroots : (primitiveRoots p K').Nonempty := by
    let zeta := IsCyclotomicExtension.zeta p K K'
    exact ⟨zeta, (mem_primitiveRoots hp.pos).2
      (IsCyclotomicExtension.zeta_spec p K K')⟩
  obtain ⟨reduction⟩ := reduction_data_index
    h93 p K' hp hroots U' U₁' hU'open hU'finite hUU₁'
      hU₁'index hU₁'exponent
  have hU'index_dvd : U'.index ∣ U.index := by
    change (U.comap norm).index ∣ U.index
    rw [U.index_comap norm]
    exact U.relIndex_dvd_index_of_normal norm.range
  have hU'index_le : U'.index ≤ U.index :=
    Nat.le_of_dvd
      (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) hU'index_dvd
  exact ⟨{
    K' := K'
    fieldK' := inferInstance
    numberFieldK' := inferInstance
    algebraKK' := inferInstance
    finiteDimensionalKK' := inferInstance
    preimage_isOpen := hU'open
    preimage_finiteIndex := hU'finite
    preimage_index_le := hU'index_le
    primeReduction := reduction }⟩

set_option maxHeartbeats 2000000 in
-- The nested cyclotomic and prime-index field structures elaborate together.
/-- **Theorem VII.9.5, induction step with roots of unity.**  Lemma 9.4
first descends from the cyclotomic field to `K`; over the cyclotomic field,
the prime-index reduction decreases the index, and a second application of
Lemma 9.4 descends from its norm extension. -/
theorem prime_reduction_cyclotomic
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V))
    (h93 : ExistenceStatementInterface.{u})
    (h94 : (∀ (K K' : Type u) [Field K] [NumberField K]
          [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
          (U : Subgroup (CK K)),
          IsOpen (U : Set (CK K)) → U.FiniteIndex →
          IdeleNormGroup K'
            (U.comap (canonicalIdeleNorm (K := K) (L := K'))) →
          IdeleNormGroup K U))
    (hpower : NormExtensionBridge.{u}) :
    ∀ (K : Type u) [Field K] [NumberField K]
      (U : Subgroup (CK K)),
      IsOpen (U : Set (CK K)) → U.FiniteIndex →
        IdeleNormGroup K U := by
  intro K _ _ U hUopen hUfinite
  induction hindex : U.index using Nat.strong_induction_on generalizing K with
  | h n ih =>
      by_cases htop : U = ⊤
      · subst U
        exact top_bridge_reciprocity h91 K
      · obtain ⟨data⟩ := cyclotomicReductionData
          h93 hpower K U hUopen hUfinite htop
        letI : Field data.K' := data.fieldK'
        letI : NumberField data.K' := data.numberFieldK'
        letI : Algebra K data.K' := data.algebraKK'
        letI : FiniteDimensional K data.K' := data.finiteDimensionalKK'
        let U' := U.comap
          (canonicalIdeleNorm (K := K) (L := data.K'))
        let reduction := data.primeReduction
        letI : Field reduction.K' := reduction.fieldK'
        letI : NumberField reduction.K' := reduction.numberFieldK'
        letI : Algebra data.K' reduction.K' := reduction.algebraKK'
        letI : FiniteDimensional data.K' reduction.K' :=
          reduction.finiteDimensionalKK'
        let W := U'.comap
          (canonicalIdeleNorm (K := data.K') (L := reduction.K'))
        have hWlt : W.index < U.index :=
          lt_of_lt_of_le reduction.preimage_index_lt data.preimage_index_le
        have hWnorm : IdeleNormGroup reduction.K' W := by
          apply ih W.index
          · simpa [hindex] using hWlt
          · exact reduction.preimage_isOpen
          · exact reduction.preimage_finiteIndex
          · rfl
        have hU'norm : IdeleNormGroup data.K' U' :=
          h94 data.K' reduction.K' U'
            data.preimage_isOpen data.preimage_finiteIndex hWnorm
        exact h94 K data.K' U hUopen hUfinite hU'norm

/-- The corrected existence-theorem statement follows from Lemmas 9.1,
9.3, and 9.4 together with the standard norm-after-extension power
identity. -/
theorem of_cyclotomic_reduction
    (K : Type u) [Field K] [NumberField K]
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V))
    (h93 : ExistenceStatementInterface.{u})
    (h94 : (∀ (K K' : Type u) [Field K] [NumberField K]
          [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
          (U : Subgroup (CK K)),
          IsOpen (U : Set (CK K)) → U.FiniteIndex →
          IdeleNormGroup K'
            (U.comap (canonicalIdeleNorm (K := K) (L := K'))) →
          IdeleNormGroup K U))
    (hpower : NormExtensionBridge.{u}) :
    EveryIndexGroup K := by
  intro U hUopen hUfinite
  exact prime_reduction_cyclotomic
    h91 h93 h94 hpower K U hUopen hUfinite

/-- The corrected existence theorem from Lemmas 9.1, 9.3, and 9.4, with
the cyclotomic and norm-power reductions discharged. -/
theorem prime_reduction_lemmas
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V))
    (h93 : ExistenceStatementInterface.{u})
    (h94 : (∀ (K K' : Type u) [Field K] [NumberField K]
          [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
          (U : Subgroup (CK K)),
          IsOpen (U : Set (CK K)) → U.FiniteIndex →
          IdeleNormGroup K'
            (U.comap (canonicalIdeleNorm (K := K) (L := K'))) →
          IdeleNormGroup K U)) :
    ∀ (K : Type u) [Field K] [NumberField K]
      (U : Subgroup (CK K)),
      IsOpen (U : Set (CK K)) → U.FiniteIndex →
        IdeleNormGroup K U :=
  prime_reduction_cyclotomic
    h91 h93 h94 normExtensionBridge

/-- Field-specific form of Theorem VII.9.5 from the three preceding
lemmas. -/
theorem of_lemmas
    (K : Type u) [Field K] [NumberField K]
    (h91 : (∀ (K : Type u) [Field K] [NumberField K]
          (U V : Subgroup (IdeleClassGroup (RingOfIntegers K) K)),
          IdeleNormGroup K U → U ≤ V → IdeleNormGroup K V))
    (h93 : ExistenceStatementInterface.{u})
    (h94 : (∀ (K K' : Type u) [Field K] [NumberField K]
          [Field K'] [NumberField K'] [Algebra K K'] [FiniteDimensional K K']
          (U : Subgroup (CK K)),
          IsOpen (U : Set (CK K)) → U.FiniteIndex →
          IdeleNormGroup K'
            (U.comap (canonicalIdeleNorm (K := K) (L := K'))) →
          IdeleNormGroup K U)) :
    EveryIndexGroup K := by
  intro U hUopen hUfinite
  exact prime_reduction_lemmas
    h91 h93 h94 K U hUopen hUfinite

end

end Towers.CField.NLimita

import Submission.NumberTheory.Locals.HenselFactorization
import Submission.NumberTheory.Locals.CompleteDVRHenselian
import Submission.NumberTheory.Locals.TeichmullerLifts
import Submission.NumberTheory.Locals.UnramifiedExtensions
import Submission.ClassField.LocalBrauer.UnramifiedExtensionExistence


/-!
# Chapter IV, Section 4: Galois structure of unramified extensions

We refine the degree-`n` unramified construction by Hensel-lifting an
irreducible factor of `X^(q^n) - X`.  This choice supplies all conjugate
roots inside the resulting fraction field and hence proves normality.  The
residue-field Frobenius can then be transported back to the field extension.
-/

namespace Submission.CField.LBrauer

noncomputable section


open Polynomial IsLocalRing
open scoped NormedField
open scoped Valued

attribute [local instance] Ideal.Quotient.field

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K]
  [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))]

private abbrev OK := Valuation.integer (NormedField.valuation (K := K))
private abbrev kK := IsLocalRing.ResidueField (OK K)

omit [IsNonarchimedeanLocalField K] in
private theorem canonical_integer_norm :
    Valuation.integer (ValuativeRel.valuation K) = OK K := by
  ext x
  simp only [Valuation.mem_integer_iff]
  rw [← (ValuativeRel.valuation K).vle_one_iff,
    ← (NormedField.valuation (K := K)).vle_one_iff]

private noncomputable def canonicalIntegerNorm :
    Valuation.integer (ValuativeRel.valuation K) ≃+* OK K :=
  RingEquiv.subringCongr (canonical_integer_norm K)

private theorem normInteger_dvr : IsDiscreteValuationRing (OK K) := by
  letI : IsDiscreteValuationRing
      (Valuation.integer (ValuativeRel.valuation K)) :=
    discrete_valuation_ring K
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (canonicalIntegerNorm K)

local instance : IsDiscreteValuationRing (OK K) :=
  normInteger_dvr K

local instance : IsAdicComplete (IsLocalRing.maximalIdeal (OK K)) (OK K) :=
  by
    simpa [OK] using
      (@Submission.NumberTheory.Milne.valued_integer_complete
        K _ _ _ (normInteger_dvr K))

local instance : HenselianLocalRing (OK K) :=
  by
    simpa [OK] using
      (@Submission.NumberTheory.Milne.valued_henselian_ring
        K _ _ _ (normInteger_dvr K))

local instance : IsFractionRing (OK K) K :=
  (Valuation.integer.integers (NormedField.valuation (K := K))).isFractionRing

local instance : Finite (kK K) :=
  by
    letI : IsDiscreteValuationRing
        (Valuation.integer (ValuativeRel.valuation K)) :=
      discrete_valuation_ring K
    letI : Finite (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation K))) :=
      local_field_residue K
    exact Finite.of_equiv
      (IsLocalRing.ResidueField
        (Valuation.integer (ValuativeRel.valuation K)))
      (IsLocalRing.ResidueField.mapEquiv
        (canonicalIntegerNorm K)).toEquiv

local instance : Fact (ringChar (kK K)).Prime :=
  ⟨CharP.char_is_prime (kK K) _⟩

private theorem adic_complete_pi
    {R ι : Type*} [CommRing R] [Finite ι]
    (I : Ideal R) [IsAdicComplete I R] :
    IsAdicComplete I (ι → R) := by
  letI := Fintype.ofFinite ι
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · constructor
    intro x hx
    funext i
    apply IsHausdorff.haus (I := I) (M := R) inferInstance
    intro n
    have hi := (hx n).map
      (LinearMap.proj i : (ι → R) →ₗ[R] R)
    simpa only [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr (LinearMap.proj_surjective i)] using hi
  · constructor
    intro f hf
    have hfcoord (i : ι) {m n : ℕ} (hmn : m ≤ n) :
        f m i ≡ f n i [SMOD (I ^ m • ⊤ : Submodule R R)] := by
      have hi := (hf hmn).map
        (LinearMap.proj i : (ι → R) →ₗ[R] R)
      simpa only [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr (LinearMap.proj_surjective i)] using hi
    choose L hL using fun i =>
      IsPrecomplete.prec (I := I) (M := R) inferInstance (hfcoord i)
    refine ⟨L, fun n => ?_⟩
    rw [SModEq.sub_mem]
    rw [show f n - L = ∑ i, (f n i - L i) •
        (Pi.basisFun R ι) i by
      rw [← (Pi.basisFun R ι).sum_equivFun (f n - L)]
      apply Finset.sum_congr rfl
      intro i hi
      simp]
    apply Submodule.sum_mem
    intro i hi
    apply Submodule.smul_mem_smul
    · have hLi := hL i n
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hLi
    · exact Submodule.mem_top

private theorem adic_complete_linear
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (e : M ≃ₗ[R] N) [IsAdicComplete I N] :
    IsAdicComplete I M := by
  refine { toIsHausdorff := ?_, toIsPrecomplete := ?_ }
  · constructor
    intro x hx
    apply e.injective
    rw [map_zero]
    apply IsHausdorff.haus (I := I) (M := N) inferInstance
    intro n
    have hn := (hx n).map e.toLinearMap
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.surjective] at hn
    change e x ≡ e 0 [SMOD (I ^ n • ⊤ : Submodule R N)] at hn
    simpa only [map_zero] using hn
  · constructor
    intro f hf
    have hef {m n : ℕ} (hmn : m ≤ n) :
        e (f m) ≡ e (f n) [SMOD (I ^ m • ⊤ : Submodule R N)] := by
      have hn := (hf hmn).map e.toLinearMap
      simpa only [Submodule.map_smul'', Submodule.map_top,
        LinearMap.range_eq_top.mpr e.surjective] using hn
    obtain ⟨L, hL⟩ :=
      IsPrecomplete.prec (I := I) (M := N) inferInstance hef
    refine ⟨e.symm L, fun n => ?_⟩
    have hn := (hL n).map e.symm.toLinearMap
    rw [Submodule.map_smul'', Submodule.map_top,
      LinearMap.range_eq_top.mpr e.symm.surjective] at hn
    change e.symm (e (f n)) ≡ e.symm L
      [SMOD (I ^ n • ⊤ : Submodule R M)] at hn
    rw [e.symm_apply_apply] at hn
    exact hn

omit [ValuativeRel K] [IsNonarchimedeanLocalField K]
  [Valuation.Compatible (NormedField.valuation (K := K))] in
private theorem adjoin_root_injective
    {f : (OK K)[X]} (hfmonic : f.Monic) (hf : Irreducible f) :
    Function.Injective (algebraMap (OK K) (AdjoinRoot f)) := by
  have hnatDegree : f.natDegree ≠ 0 := by
    intro hdegree
    have hfOne : f = 1 := hfmonic.natDegree_eq_zero.mp hdegree
    exact hf.not_isUnit (hfOne ▸ isUnit_one)
  have hdegree : f.degree ≠ 0 := by
    rw [degree_eq_natDegree hf.ne_zero]
    exact_mod_cast hnatDegree
  simpa [AdjoinRoot.algebraMap_eq] using
    AdjoinRoot.of.injective_of_degree_ne_zero hdegree

@[implicit_reducible]
private noncomputable def frobeniusFractionAlgebra
    {f : (OK K)[X]} (hfmonic : f.Monic) (hf : Irreducible f) :
    Algebra K (FractionRing (AdjoinRoot f)) := by
  let U := AdjoinRoot f
  letI : IsDomain U := AdjoinRoot.isDomain_of_prime hf.prime
  letI : Algebra U (FractionRing U) := OreLocalization.instAlgebra
  letI : Algebra (OK K) (FractionRing U) :=
    ((algebraMap U (FractionRing U)).comp (algebraMap (OK K) U)).toAlgebra
  have hOf : Function.Injective (algebraMap (OK K) U) :=
    adjoin_root_injective K hfmonic hf
  have hinjective : Function.Injective
      (algebraMap (OK K) (FractionRing U)) := by
    change Function.Injective
      ((algebraMap U (FractionRing U)).comp (algebraMap (OK K) U))
    exact (IsFractionRing.injective U (FractionRing U)).comp hOf
  exact (IsFractionRing.lift
    hinjective).toAlgebra

/-- A degree-`n` irreducible factor of `X^(q^n) - X` over the residue field
lifts to a monic factor over the integer ring. -/
theorem frobenius_hensel_factor (n : ℕ) [NeZero n] :
    let q := Nat.card (kK K)
    ∃ f h : (OK K)[X],
      f.Monic ∧ h.Monic ∧
        X ^ q ^ n - X = f * h ∧
        f.natDegree = n ∧
        Irreducible (f.map (IsLocalRing.residue (OK K))) ∧
        (f.map (IsLocalRing.residue (OK K))).Separable := by
  let A := OK K
  let k := kK K
  let q := Nat.card k
  let p := ringChar k
  letI : Finite k := inferInstance
  letI : Fintype k := Fintype.ofFinite k
  letI : Fact p.Prime := ⟨CharP.char_is_prime k _⟩
  let l := FiniteField.Extension k p n
  letI : Fintype l := Fintype.ofFinite l
  obtain ⟨a, ha⟩ := Field.exists_primitive_element k l
  let g₀ : k[X] := minpoly k a
  have hg₀monic : g₀.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral a)
  have hg₀irred : Irreducible g₀ :=
    minpoly.irreducible (Algebra.IsIntegral.isIntegral a)
  have hg₀degree : g₀.natDegree = n := by
    rw [← FiniteField.finrank_extension k p n]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq k a).mp ha
  let P₀ : k[X] := X ^ q ^ n - X
  have haP₀ : aeval a P₀ = 0 := by
    rw [aeval_def]
    simp only [P₀, eval₂_sub, eval₂_pow, eval₂_X]
    rw [← FiniteField.natCard_extension k p n]
    exact sub_eq_zero.mpr (by
      simpa [Nat.card_eq_fintype_card] using FiniteField.pow_card a)
  have hg₀dvd : g₀ ∣ P₀ := minpoly.dvd k a haP₀
  obtain ⟨h₀, hh₀⟩ := hg₀dvd
  have hqone : 1 < q := by
    simpa [q, Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := k)
  have hQpos : 0 < q ^ n := (Nat.one_lt_pow (NeZero.ne n) hqone).le
  have hP₀monic : P₀.Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast (Nat.one_lt_pow (NeZero.ne n) hqone)
  have hh₀monic : h₀.Monic := by
    apply hg₀monic.of_mul_monic_left
    rw [← hh₀]
    exact hP₀monic
  have hqcast : (q : k) = 0 := by
    simp [q, Nat.card_eq_fintype_card]
  have hQcast : (q ^ n : k) = 0 := by
    simp [hqcast, NeZero.ne n]
  have hP₀derivative : P₀.derivative = -1 := by
    simp [P₀, derivative_sub, derivative_X_pow, hQcast]
  have hP₀sep : P₀.Separable := by
    rw [separable_def, hP₀derivative]
    exact isCoprime_one_right.neg_right
  have hcoprime₀ : IsCoprime g₀ h₀ := by
    rw [hh₀] at hP₀sep
    exact hP₀sep.isCoprime
  let P : A[X] := X ^ q ^ n - X
  have hPmonic : P.Monic := by
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast (Nat.one_lt_pow (NeZero.ne n) hqone)
  have hPmap : P.map (IsLocalRing.residue A) = g₀ * h₀ := by
    rw [← hh₀]
    simp [P, P₀]
  obtain ⟨f, h, hfmonic, hhmonic, hfactor, hfmap, _hhmap, _hcoprime⟩ :=
    Submission.NumberTheory.Milne.adic_hensel_factorization
      P hPmonic g₀ h₀ hg₀monic hh₀monic hPmap hcoprime₀
  have hfdegree : f.natDegree = n := by
    rw [← hg₀degree, ← hfmap, hfmonic.natDegree_map]
  refine ⟨f, h, hfmonic, hhmonic, hfactor, hfdegree, ?_, ?_⟩
  · simpa [A] using hfmap ▸ hg₀irred
  · simpa [A] using hfmap ▸ Algebra.IsSeparable.isSeparable k a

private noncomputable def adjoinRootResidueEquiv
    (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A[X]) [IsLocalRing (AdjoinRoot f)]
    (hmax : maximalIdeal (AdjoinRoot f) =
      (maximalIdeal A).map (AdjoinRoot.of f)) :
    AdjoinRoot (f.map (residue A)) ≃+* ResidueField (AdjoinRoot f) := by
  let p := maximalIdeal A
  exact
    (AdjoinRoot.quotEquivQuotMap f p).symm.toRingEquiv.trans
      (Ideal.quotEquivOfEq hmax.symm)

set_option synthInstance.maxHeartbeats 100000 in
-- The quotient-residue comparison below unfolds transported local-ring instances.
set_option maxHeartbeats 1000000 in
/-- The residue field of the local algebra defined by the lifted factor has
the same degree `n` as its fraction field. -/
theorem residue_frobenius_factor
    (n : ℕ) [NeZero n] (f : (OK K)[X])
    (hfmonic : f.Monic) (hfdegree : f.natDegree = n)
    (hfred : Irreducible (f.map (IsLocalRing.residue (OK K)))) :
    let U := AdjoinRoot f
    ∃ hlocal : IsLocalRing U,
      letI := hlocal
      ∃ hlocalHom : IsLocalHom (algebraMap (OK K) U),
        letI := hlocalHom
        Module.finrank (kK K) (IsLocalRing.ResidueField U) = n := by
  change ∃ hlocal : IsLocalRing (AdjoinRoot f),
    letI := hlocal
    ∃ hlocalHom : IsLocalHom (algebraMap (OK K) (AdjoinRoot f)),
      letI := hlocalHom
      Module.finrank (kK K)
        (IsLocalRing.ResidueField (AdjoinRoot f)) = n
  let A := OK K
  let k := kK K
  have hfirr : Irreducible f :=
    hfmonic.irreducible_of_irreducible_map (residue (OK K)) f hfred
  letI : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime hfirr.prime
  let hlocal : IsLocalRing (AdjoinRoot f) :=
    adjoin_ring_irreducible
      (OK K) f hfmonic hfred
  letI : IsLocalRing (AdjoinRoot f) := hlocal
  let p : Ideal (OK K) := maximalIdeal (OK K)
  have hmax : maximalIdeal (AdjoinRoot f) =
      p.map (AdjoinRoot.of f) :=
    adjoin_irreducible_residue
      (OK K) f hfmonic hfred
  let hlocalHom : IsLocalHom (algebraMap (OK K) (AdjoinRoot f)) :=
    ((IsLocalRing.local_hom_TFAE
      (algebraMap (OK K) (AdjoinRoot f))).out 2 0).mp (by
      simpa [AdjoinRoot.algebraMap_eq] using hmax.symm.le)
  letI : IsLocalHom (algebraMap (OK K) (AdjoinRoot f)) := hlocalHom
  let g : k[X] := f.map (residue (OK K))
  let eRing : AdjoinRoot g ≃+*
      IsLocalRing.ResidueField (AdjoinRoot f) :=
    adjoinRootResidueEquiv (OK K) f hmax
  letI : Module.Finite k (AdjoinRoot g) :=
    (hfmonic.map (residue (OK K))).finite_adjoinRoot
  letI : Finite (AdjoinRoot g) := Module.finite_of_finite k
  letI : Finite (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Finite.of_equiv (AdjoinRoot g) eRing.toEquiv
  letI : Module.Finite k (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    by infer_instance
  have hcard : Nat.card (AdjoinRoot g) =
      Nat.card (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Nat.card_congr eRing.toEquiv
  have hpowers : Nat.card k ^ Module.finrank k (AdjoinRoot g) =
      Nat.card k ^ Module.finrank k
        (IsLocalRing.ResidueField (AdjoinRoot f)) := by
    rw [← Module.natCard_eq_pow_finrank, ← Module.natCard_eq_pow_finrank]
    exact hcard
  have hfinrank : Module.finrank k (AdjoinRoot g) =
      Module.finrank k (IsLocalRing.ResidueField (AdjoinRoot f)) :=
    Nat.pow_right_injective (Finite.one_lt_card (α := k)) hpowers
  refine ⟨hlocal, hlocalHom, ?_⟩
  rw [← hfinrank,
    (AdjoinRoot.powerBasis' (hfmonic.map (residue (OK K)))).finrank]
  change (f.map (residue (OK K))).natDegree = n
  exact (hfmonic.natDegree_map (residue (OK K))).trans hfdegree

/-- The full Frobenius polynomial splits in the fraction field defined by
any degree-`n` Hensel factor with irreducible reduction. -/
theorem splits_fraction_field
    (n : ℕ) [NeZero n] (f : (OK K)[X])
    (hfmonic : f.Monic) (hfdegree : f.natDegree = n)
    (hfred : Irreducible (f.map (IsLocalRing.residue (OK K)))) :
    let U := AdjoinRoot f
    let hfirr : Irreducible f :=
      hfmonic.irreducible_of_irreducible_map
        (IsLocalRing.residue (OK K)) f hfred
    letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
    letI : Algebra K (FractionRing U) :=
      frobeniusFractionAlgebra K hfmonic hfirr
    (((X ^ (Nat.card (kK K)) ^ n - X : (OK K)[X]).map
      (algebraMap (OK K) K)).map
        (algebraMap K (FractionRing U))).Splits := by
  let A := OK K
  let k := kK K
  let q := Nat.card k
  let U := AdjoinRoot f
  have hfirr : Irreducible f :=
    hfmonic.irreducible_of_irreducible_map
      (IsLocalRing.residue A) f hfred
  letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
  obtain ⟨hlocal, hlocalHom, hresdegree⟩ :=
    residue_frobenius_factor K n f hfmonic hfdegree hfred
  letI : IsLocalRing U := hlocal
  letI : IsLocalHom (algebraMap A U) := hlocalHom
  letI : Module.Finite A U := hfmonic.finite_adjoinRoot
  let b := (AdjoinRoot.powerBasis' hfmonic).basis
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A)
      (Fin (AdjoinRoot.powerBasis' hfmonic).dim → A) :=
    adic_complete_pi (IsLocalRing.maximalIdeal A)
  letI : IsAdicComplete (IsLocalRing.maximalIdeal A) U :=
    adic_complete_linear
      (IsLocalRing.maximalIdeal A) b.equivFun
  have hmax : IsLocalRing.maximalIdeal U =
      (IsLocalRing.maximalIdeal A).map (algebraMap A U) := by
    simpa [AdjoinRoot.algebraMap_eq] using
      (adjoin_irreducible_residue
        A f hfmonic hfred)
  letI : IsAdicComplete
      ((IsLocalRing.maximalIdeal A).map (algebraMap A U)) U :=
    (IsAdicComplete.map_algebraMap_iff
      (I := IsLocalRing.maximalIdeal A) (M := U)).mpr inferInstance
  letI : IsAdicComplete (IsLocalRing.maximalIdeal U) U := by
    rw [hmax]
    infer_instance
  letI : HenselianLocalRing U :=
    { toIsLocalRing := hlocal
      is_henselian := by
        intro p hp a ha hpa
        exact @HenselianRing.is_henselian U _
          (IsLocalRing.maximalIdeal U)
          (IsAdicComplete.henselianRing U
            (IsLocalRing.maximalIdeal U))
          p hp a ha
          (hpa.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal U))) }
  let kU := IsLocalRing.ResidueField U
  letI : Fintype k := Fintype.ofFinite k
  letI : Module.Finite k kU := Module.finite_of_finrank_pos (by
    rw [hresdegree]
    exact NeZero.pos n)
  letI : Finite kU := Module.finite_of_finite k
  letI : Fintype kU := Fintype.ofFinite kU
  have hkUcard : Fintype.card kU = q ^ n := by
    calc
      Fintype.card kU = Fintype.card k ^ Module.finrank k kU :=
        Module.card_eq_pow_finrank
      _ = Fintype.card k ^ n := by rw [hresdegree]
      _ = q ^ n := by rw [Fintype.card_eq_nat_card]
  choose lift hliftRoot hliftResidue using fun a0 : kU =>
    Submission.NumberTheory.Milne.exists_teichmullerLift U a0
  have hliftInjective : Function.Injective lift := by
    intro a0 b0 hab
    have := congrArg (IsLocalRing.residue U) hab
    simpa only [hliftResidue] using this
  let P : U[X] := X ^ q ^ n - X
  have hliftRootP (a0 : kU) : P.IsRoot (lift a0) := by
    rw [hkUcard] at hliftRoot
    simpa [P] using hliftRoot a0
  let roots : Finset U := Finset.univ.image lift
  have hrootsCard : roots.card = q ^ n := by
    rw [Finset.card_image_of_injective _ hliftInjective,
      Finset.card_univ, hkUcard]
  have hqone : 1 < q := by
    simpa [q, Nat.card_eq_fintype_card] using
      Fintype.one_lt_card (α := k)
  have hPmonic : P.Monic := by
    dsimp [P]
    apply monic_X_pow_sub
    rw [degree_X]
    exact_mod_cast (Nat.one_lt_pow (NeZero.ne n) hqone)
  have hPnatDegree : P.natDegree = q ^ n := by
    dsimp [P]
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · exact natDegree_X_pow (q ^ n)
    · simpa using Nat.one_lt_pow (NeZero.ne n) hqone
  have hrootsSub : roots ⊆ P.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨a0, -, rfl⟩ := hx
    rw [Multiset.mem_toFinset, mem_roots]
    · exact hliftRootP a0
    · exact hPmonic.ne_zero
  have hrootsLower : q ^ n ≤ P.roots.card := by
    calc
      q ^ n = roots.card := hrootsCard.symm
      _ ≤ P.roots.toFinset.card := Finset.card_le_card hrootsSub
      _ ≤ P.roots.card := Multiset.toFinset_card_le _
  have hPsplits : P.Splits := by
    rw [splits_iff_card_roots]
    exact Nat.le_antisymm (card_roots' P) <| by
      simpa [hPnatDegree] using hrootsLower
  let L := FractionRing U
  let uFracAlgebra : Algebra U L := OreLocalization.instAlgebra
  letI : SMul U L := uFracAlgebra.toSMul
  letI : Algebra U L := uFracAlgebra
  let aFracAlgebra : Algebra A L :=
    ((algebraMap U L).comp (algebraMap A U)).toAlgebra
  letI : SMul A L := aFracAlgebra.toSMul
  letI : Algebra A L := aFracAlgebra
  letI : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).2 <| by
      change Function.Injective
        ((algebraMap U L).comp (algebraMap A U))
      exact (IsFractionRing.injective U L).comp
        (adjoin_root_injective K hfmonic hfirr)
  letI : Algebra K L := frobeniusFractionAlgebra K hfmonic hfirr
  letI : IsScalarTower A U L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap A L x = algebraMap K L (algebraMap A K x)
    exact IsFractionRing.lift_algebraMap
      (FaithfulSMul.algebraMap_injective A L) x |>.symm)
  have hmaps : (algebraMap K L).comp (algebraMap A K) =
      (algebraMap U L).comp (algebraMap A U) :=
    (IsScalarTower.algebraMap_eq A K L).symm.trans
      (IsScalarTower.algebraMap_eq A U L)
  dsimp only
  rw [map_map, hmaps]
  simpa [P, map_map, q, Nat.card_eq_fintype_card] using
    hPsplits.map (algebraMap U L)

/-- The preceding splitting result, with the exponent expressed using the
canonical residue field notation for `K`. -/
theorem frobenius_splits_fraction
    (n : ℕ) [NeZero n] (f : (OK K)[X])
    (hfmonic : f.Monic) (hfdegree : f.natDegree = n)
    (hfred : Irreducible (f.map (IsLocalRing.residue (OK K)))) :
    let U := AdjoinRoot f
    let hfirr : Irreducible f :=
      hfmonic.irreducible_of_irreducible_map
        (IsLocalRing.residue (OK K)) f hfred
    letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
    letI : Algebra K (FractionRing U) :=
      frobeniusFractionAlgebra K hfmonic hfirr
    ((X ^ (Nat.card 𝓀[K]) ^ n - X : K[X]).map
      (algebraMap K (FractionRing U))).Splits := by
  let U := AdjoinRoot f
  have hfirr : Irreducible f :=
    hfmonic.irreducible_of_irreducible_map
      (IsLocalRing.residue (OK K)) f hfred
  letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
  letI : Algebra K (FractionRing U) :=
    frobeniusFractionAlgebra K hfmonic hfirr
  have hcard : Nat.card (kK K) = Nat.card 𝓀[K] := rfl
  rw [← hcard]
  simpa using
    splits_fraction_field
      K n f hfmonic hfdegree hfred

/-- The Hensel-lifted factor splits in the fraction field of its local
adjoining-root algebra. -/
theorem frobenius_hensel_splits
    (n : ℕ) [NeZero n] (f h : (OK K)[X])
    (hfmonic : f.Monic) (hfdegree : f.natDegree = n)
    (hfactor : X ^ (Nat.card (kK K)) ^ n - X = f * h)
    (hfred : Irreducible (f.map (IsLocalRing.residue (OK K)))) :
    let U := AdjoinRoot f
    let hfirr : Irreducible f :=
      hfmonic.irreducible_of_irreducible_map
        (IsLocalRing.residue (OK K)) f hfred
    letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
    letI : Algebra K (FractionRing U) :=
      frobeniusFractionAlgebra K hfmonic hfirr
    ((f.map (algebraMap (OK K) K)).map
      (algebraMap K (FractionRing U))).Splits := by
  let A := OK K
  let k := kK K
  let q := Nat.card k
  let g : k[X] := f.map (IsLocalRing.residue A)
  let U := AdjoinRoot f
  have hfirr : Irreducible f :=
    hfmonic.irreducible_of_irreducible_map (IsLocalRing.residue A) f hfred
  letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
  obtain ⟨hlocal, hlocalHom, hresdegree⟩ :=
    residue_frobenius_factor K n f hfmonic hfdegree hfred
  letI : IsLocalRing U := hlocal
  letI : IsLocalHom (algebraMap A U) := hlocalHom
  let kU := IsLocalRing.ResidueField U
  letI : Fintype k := Fintype.ofFinite k
  letI : Module.Finite k kU := Module.finite_of_finrank_pos (by
    rw [hresdegree]
    exact NeZero.pos n)
  letI : Finite kU := Module.finite_of_finite k
  let alpha : U := AdjoinRoot.root f
  let alphabar : kU := IsLocalRing.residue U alpha
  have hcompResidue :
      (algebraMap k kU).comp (IsLocalRing.residue A) =
        (IsLocalRing.residue U).comp (algebraMap A U) := by
    ext x
    exact (IsLocalRing.ResidueField.algebraMap_residue x).symm
  have halphaRoot :
      (f.map (algebraMap A U)).IsRoot alpha := AdjoinRoot.isRoot_root f
  have halphabarRoot : aeval alphabar g = 0 := by
    rw [IsRoot, eval_map] at halphaRoot
    have hx := congrArg (IsLocalRing.residue U) halphaRoot
    rw [map_zero] at hx
    simpa [g, alphabar] using
      (map_aeval_eq_aeval_map hcompResidue f alpha).symm.trans hx
  have hminpoly : minpoly k alphabar = g :=
    (minpoly.eq_of_irreducible_of_monic hfred halphabarRoot
      (hfmonic.map (IsLocalRing.residue A))).symm
  have hprimitive : IntermediateField.adjoin k ({alphabar} : Set kU) = ⊤ := by
    apply (Field.primitive_element_iff_minpoly_natDegree_eq k alphabar).mpr
    rw [hminpoly, show g.natDegree = n by
      simpa [g] using (hfmonic.natDegree_map (IsLocalRing.residue A)).trans hfdegree,
      hresdegree]
  let sigma : Gal(kU / k) := FiniteField.frobeniusAlgEquivOfAlgebraic k kU
  have hsigma_apply (i : ℕ) :
      (sigma ^ i) alphabar = alphabar ^ q ^ i := by
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      Fintype.card_eq_nat_card]
  have hsigmaRoot (i : ℕ) : aeval ((sigma ^ i) alphabar) g = 0 := by
    have hsigmaComp :
        (algebraMap k kU).comp (RingHom.id k) =
          (sigma ^ i).toRingHom.comp (algebraMap k kU) := by
      ext x
      simp only [RingHom.comp_apply, RingHom.id_apply]
      exact ((sigma ^ i).commutes x).symm
    have hx := map_aeval_eq_aeval_map hsigmaComp g alphabar
    simpa [halphabarRoot] using hx.symm
  let P : A[X] := X ^ q ^ n - X
  let fU : U[X] := f.map (algebraMap A U)
  let hU : U[X] := h.map (algebraMap A U)
  have hfactorU : P.map (algebraMap A U) = fU * hU := by
    have hx := congrArg (Polynomial.map (algebraMap A U)) hfactor
    simpa [P, q, fU, hU] using hx
  have halphaQ : alpha ^ q ^ n = alpha := by
    have hrootP : (P.map (algebraMap A U)).IsRoot alpha := by
      rw [hfactorU, IsRoot, eval_mul, show fU.eval alpha = 0 from halphaRoot]
      simp
    exact sub_eq_zero.mp (by simpa [P, IsRoot] using hrootP)
  let beta : Fin n → U := fun i ↦ alpha ^ q ^ i.1
  have hbetaP (i : Fin n) :
      (P.map (algebraMap A U)).IsRoot (beta i) := by
    have heq : (alpha ^ q ^ i.1) ^ q ^ n = alpha ^ q ^ i.1 := by
      rw [← pow_mul, mul_comm (q ^ i.1) (q ^ n), pow_mul, halphaQ]
    simpa [P, beta, IsRoot] using sub_eq_zero.mpr heq
  have hresBeta (i : Fin n) :
      IsLocalRing.residue U (beta i) = (sigma ^ i.1) alphabar := by
    rw [hsigma_apply]
    simp [beta, alphabar]
  let Pbar : k[X] := X ^ q ^ n - X
  let hbar : k[X] := h.map (IsLocalRing.residue A)
  have hfactorBar : Pbar = g * hbar := by
    have hx := congrArg (Polynomial.map (IsLocalRing.residue A)) hfactor
    simpa [Pbar, g, hbar, q] using hx
  have hqcast : (q : k) = 0 := by
    simp [q, Nat.card_eq_fintype_card]
  have hQcast : (q ^ n : k) = 0 := by
    simp [hqcast, NeZero.ne n]
  have hPbarDerivative : Pbar.derivative = -1 := by
    simp [Pbar, derivative_sub, derivative_X_pow, hQcast]
  have hPbarSeparable : Pbar.Separable := by
    rw [separable_def, hPbarDerivative]
    exact isCoprime_one_right.neg_right
  have hcoprimeBar : IsCoprime g hbar := by
    rw [hfactorBar] at hPbarSeparable
    exact hPbarSeparable.isCoprime
  have hhbarNe (i : Fin n) :
      aeval ((sigma ^ i.1) alphabar) hbar ≠ 0 := by
    rcases aeval_ne_zero_of_isCoprime hcoprimeBar
      ((sigma ^ i.1) alphabar) with hg | hh
    · exact (hg (hsigmaRoot i.1)).elim
    · exact hh
  have hhUNe (i : Fin n) : hU.eval (beta i) ≠ 0 := by
    intro hz
    apply hhbarNe i
    dsimp [hU] at hz
    rw [eval_map] at hz
    have hx := congrArg (IsLocalRing.residue U) hz
    rw [map_zero] at hx
    have hmap := map_aeval_eq_aeval_map hcompResidue h (beta i)
    simpa [aeval_def, hbar, hresBeta i] using hmap.symm.trans hx
  have hbetaRoot (i : Fin n) : fU.IsRoot (beta i) := by
    have hp := hbetaP i
    rw [hfactorU, IsRoot, eval_mul] at hp
    exact (mul_eq_zero.mp hp).resolve_right (hhUNe i)
  have hbetaInjective : Function.Injective beta := by
    intro i j hij
    have hpoint : (sigma ^ i.1) alphabar = (sigma ^ j.1) alphabar := by
      rw [← hresBeta i, ← hresBeta j, hij]
    have hsigmaEq : sigma ^ i.1 = sigma ^ j.1 := by
      apply AlgEquiv.ext
      intro x
      apply IntermediateField.adjoin_induction
        (s := ({alphabar} : Set kU))
        (p := fun y _ => (sigma ^ i.1) y = (sigma ^ j.1) y)
        (mem := by
          intro y hy
          simpa only [Set.mem_singleton_iff] using hy ▸ hpoint)
        (algebraMap := fun y : k => by simp)
        (add := fun y z _ _ hy hz => by simpa using congrArg₂ (· + ·) hy hz)
        (inv := fun y _ hy => by simpa using congrArg Inv.inv hy)
        (mul := fun y z _ _ hy hz => by simpa using congrArg₂ (· * ·) hy hz)
      rw [hprimitive]
      exact IntermediateField.mem_top
    have hbij := FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k kU
    rw [hresdegree] at hbij
    exact Fin.ext (congrArg Fin.val (hbij.injective hsigmaEq))
  let roots : Finset U := Finset.univ.image beta
  have hrootsCard : roots.card = n := by
    rw [Finset.card_image_of_injective _ hbetaInjective,
      Finset.card_univ, Fintype.card_fin]
  have hrootsSub : roots ⊆ fU.roots.toFinset := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, -, rfl⟩ := hx
    rw [Multiset.mem_toFinset,
      mem_roots (hfmonic.map (algebraMap A U)).ne_zero]
    exact hbetaRoot i
  have hrootsLower : n ≤ fU.roots.card := by
    calc
      n = roots.card := hrootsCard.symm
      _ ≤ fU.roots.toFinset.card := Finset.card_le_card hrootsSub
      _ ≤ fU.roots.card := Multiset.toFinset_card_le _
  have hfUsplits : fU.Splits := by
    rw [splits_iff_card_roots]
    exact Nat.le_antisymm (card_roots' fU) <| by
      simpa [fU, hfmonic.natDegree_map, hfdegree] using hrootsLower
  let L := FractionRing U
  let uFracAlgebra : Algebra U L := OreLocalization.instAlgebra
  letI : SMul U L := uFracAlgebra.toSMul
  letI : Algebra U L := uFracAlgebra
  let aFracAlgebra : Algebra A L :=
    ((algebraMap U L).comp (algebraMap A U)).toAlgebra
  letI : SMul A L := aFracAlgebra.toSMul
  letI : Algebra A L := aFracAlgebra
  letI : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).2 <| by
      change Function.Injective
        ((algebraMap U L).comp (algebraMap A U))
      exact (IsFractionRing.injective U L).comp
        (adjoin_root_injective K hfmonic hfirr)
  letI : Algebra K L := frobeniusFractionAlgebra K hfmonic hfirr
  letI : IsScalarTower A U L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap A L x = algebraMap K L (algebraMap A K x)
    exact IsFractionRing.lift_algebraMap
      (FaithfulSMul.algebraMap_injective A L) x |>.symm)
  have hmaps : (algebraMap K L).comp (algebraMap A K) =
      (algebraMap U L).comp (algebraMap A U) :=
    (IsScalarTower.algebraMap_eq A K L).symm.trans
      (IsScalarTower.algebraMap_eq A U L)
  dsimp only
  rw [map_map, hmaps]
  simpa [fU, map_map] using hfUsplits.map (algebraMap U L)

/-- The fraction field defined by a Frobenius Hensel factor is Galois over
the local field. -/
theorem fraction_frobenius_factor
    (n : ℕ) [NeZero n] (f h : (OK K)[X])
    (hfmonic : f.Monic) (hfdegree : f.natDegree = n)
    (hfactor : X ^ (Nat.card (kK K)) ^ n - X = f * h)
    (hfred : Irreducible (f.map (IsLocalRing.residue (OK K)))) :
    let U := AdjoinRoot f
    let hfirr : Irreducible f :=
      hfmonic.irreducible_of_irreducible_map
        (IsLocalRing.residue (OK K)) f hfred
    letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
    letI : Algebra K (FractionRing U) :=
      frobeniusFractionAlgebra K hfmonic hfirr
    IsGalois K (FractionRing U) := by
  let A := OK K
  let U := AdjoinRoot f
  have hfirr : Irreducible f :=
    hfmonic.irreducible_of_irreducible_map (IsLocalRing.residue A) f hfred
  letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).2
      (adjoin_root_injective K hfmonic hfirr)
  obtain ⟨hlocal, hlocalHom, _hresdegree⟩ :=
    residue_frobenius_factor K n f hfmonic hfdegree hfred
  letI : IsLocalRing U := hlocal
  letI : IsLocalHom (algebraMap A U) := hlocalHom
  let L := FractionRing U
  let uFracAlgebra : Algebra U L := OreLocalization.instAlgebra
  letI : SMul U L := uFracAlgebra.toSMul
  letI : Algebra U L := uFracAlgebra
  let aFracAlgebra : Algebra A L :=
    ((algebraMap U L).comp (algebraMap A U)).toAlgebra
  letI : SMul A L := aFracAlgebra.toSMul
  letI : Algebra A L := aFracAlgebra
  letI : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).2 <| by
      change Function.Injective
        ((algebraMap U L).comp (algebraMap A U))
      exact (IsFractionRing.injective U L).comp
        (FaithfulSMul.algebraMap_injective A U)
  letI : Algebra K L := frobeniusFractionAlgebra K hfmonic hfirr
  letI : IsScalarTower A U L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap A L x = algebraMap K L (algebraMap A K x)
    exact IsFractionRing.lift_algebraMap
      (FaithfulSMul.algebraMap_injective A L) x |>.symm)
  letI : Module.Finite A U := hfmonic.finite_adjoinRoot
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : Fintype (kK K) := Fintype.ofFinite (kK K)
  letI : Algebra.FormallyUnramified A U :=
    formally_irreducible_separable
      A f hfmonic hfred (PerfectField.separable_of_irreducible hfred)
  have hLdegree : Module.finrank K L = n := by
    calc
      Module.finrank K L = Module.finrank A U :=
        Algebra.IsAlgebraic.finrank_of_isFractionRing A K U L
      _ = f.natDegree := (AdjoinRoot.powerBasis' hfmonic).finrank
      _ = n := hfdegree
  letI : Module.Finite K L := Module.finite_of_finrank_pos (by
    rw [hLdegree]
    exact NeZero.pos n)
  letI : Algebra.FormallyUnramified U L := inferInstance
  letI : Algebra.FormallyUnramified A L :=
    Algebra.FormallyUnramified.comp A U L
  letI : Algebra.FormallyUnramified K L :=
    Algebra.FormallyUnramified.of_restrictScalars A K L
  letI : Algebra.IsSeparable K L :=
    Algebra.FormallyUnramified.isSeparable K L
  let fK : K[X] := f.map (algebraMap A K)
  have hfKirred : Irreducible fK := by
    exact (hfmonic.irreducible_iff_irreducible_map_fraction_map).mp hfirr
  let alpha : U := AdjoinRoot.root f
  let alphaL : L := algebraMap U L alpha
  have halphaRoot : (f.map (algebraMap A U)).IsRoot alpha :=
    AdjoinRoot.isRoot_root f
  have hmaps :
      (algebraMap K L).comp (algebraMap A K) =
        (algebraMap U L).comp (algebraMap A U) := by
    exact (IsScalarTower.algebraMap_eq A K L).symm.trans
      (IsScalarTower.algebraMap_eq A U L)
  have halphaLRoot : aeval alphaL fK = 0 := by
    rw [IsRoot, eval_map] at halphaRoot
    have hx := congrArg (algebraMap U L) halphaRoot
    rw [map_zero] at hx
    simpa [fK, alphaL] using
      (map_aeval_eq_aeval_map hmaps f alpha).symm.trans hx
  have hminpoly : minpoly K alphaL = fK :=
    (minpoly.eq_of_irreducible_of_monic hfKirred halphaLRoot
      (hfmonic.map (algebraMap A K))).symm
  have hprimitive : IntermediateField.adjoin K ({alphaL} : Set L) = ⊤ := by
    apply (Field.primitive_element_iff_minpoly_natDegree_eq K alphaL).mpr
    rw [hminpoly, show fK.natDegree = n by
      simpa [fK] using (hfmonic.natDegree_map (algebraMap A K)).trans hfdegree,
      hLdegree]
  have hsplit : (fK.map (algebraMap K L)).Splits :=
    frobenius_hensel_splits K n f h hfmonic hfdegree hfactor hfred
  have hnormal : Normal K L := by
    rw [normal_iff]
    intro x
    refine ⟨Algebra.IsIntegral.isIntegral x, ?_⟩
    apply IntermediateField.splits_of_mem_adjoin
      (F := K) (K := L) (L := L) (S := ({alphaL} : Set L))
    · intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact ⟨Algebra.IsIntegral.isIntegral alphaL, by simpa [hminpoly] using hsplit⟩
    · rw [hprimitive]
      exact IntermediateField.mem_top
  exact (isGalois_iff.mpr ⟨inferInstance, hnormal⟩)

set_option maxHeartbeats 5000000 in
-- The Frobenius construction elaborates the full integral and fraction-field towers.
set_option synthInstance.maxHeartbeats 100000 in
-- Residue-field module synthesis unfolds the lifted integral model.
/-- Arithmetic Frobenius lifts from the residue extension to the Galois
group of the unramified fraction field.  It has order `n` and generates the
whole Galois group. -/
theorem frobenius_generator_factor
    (n : ℕ) [NeZero n] (f h : (OK K)[X])
    (hfmonic : f.Monic) (hfdegree : f.natDegree = n)
    (hfactor : X ^ (Nat.card (kK K)) ^ n - X = f * h)
    (hfred : Irreducible (f.map (IsLocalRing.residue (OK K)))) :
    let U := AdjoinRoot f
    let hfirr : Irreducible f :=
      hfmonic.irreducible_of_irreducible_map
        (IsLocalRing.residue (OK K)) f hfred
    letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
    letI : Algebra K (FractionRing U) :=
      frobeniusFractionAlgebra K hfmonic hfirr
    IsCyclic Gal(FractionRing U / K) ∧
      ∃ φ : Gal(FractionRing U / K),
        orderOf φ = n ∧ ∀ σ : Gal(FractionRing U / K),
          ∃ i < n, φ ^ i = σ := by
  let A := OK K
  let k := kK K
  letI : Fintype k := Fintype.ofFinite k
  let U := AdjoinRoot f
  have hfirr : Irreducible f :=
    hfmonic.irreducible_of_irreducible_map (IsLocalRing.residue A) f hfred
  letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).2
      (adjoin_root_injective K hfmonic hfirr)
  obtain ⟨hlocal, hlocalHom, hresdegree⟩ :=
    residue_frobenius_factor K n f hfmonic hfdegree hfred
  letI : IsLocalRing U := hlocal
  letI : IsLocalHom (algebraMap A U) := hlocalHom
  letI : Module.Finite A U := hfmonic.finite_adjoinRoot
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : Algebra.FormallyUnramified A U :=
    formally_irreducible_separable
      A f hfmonic hfred (PerfectField.separable_of_irreducible hfred)
  letI : IsDedekindDomain U := isDedekindDomain.of_formallyUnramified A U
  have hnfield : ¬ IsField U := by
    intro hU
    exact IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField
        (FaithfulSMul.algebraMap_injective A U) hU)
  letI : IsDiscreteValuationRing U :=
    ((IsDiscreteValuationRing.TFAE U hnfield).out 2 0).mp
      (inferInstance : IsDedekindDomain U)
  let L := FractionRing U
  let uFracAlgebra : Algebra U L := OreLocalization.instAlgebra
  letI : SMul U L := uFracAlgebra.toSMul
  letI : Algebra U L := uFracAlgebra
  let aFracAlgebra : Algebra A L :=
    ((algebraMap U L).comp (algebraMap A U)).toAlgebra
  letI : SMul A L := aFracAlgebra.toSMul
  letI : Algebra A L := aFracAlgebra
  letI : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).2 <| by
      change Function.Injective
        ((algebraMap U L).comp (algebraMap A U))
      exact (IsFractionRing.injective U L).comp
        (FaithfulSMul.algebraMap_injective A U)
  letI : Algebra K L := frobeniusFractionAlgebra K hfmonic hfirr
  letI : IsScalarTower A U L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap A L x = algebraMap K L (algebraMap A K x)
    exact IsFractionRing.lift_algebraMap
      (FaithfulSMul.algebraMap_injective A L) x |>.symm)
  letI : Module.Finite K L := Module.finite_of_finrank_pos (by
    rw [Algebra.IsAlgebraic.finrank_of_isFractionRing A K U L]
    have hAU : Module.finrank A U = n :=
      (AdjoinRoot.powerBasis' hfmonic).finrank.trans hfdegree
    simpa only [hAU] using NeZero.pos n)
  letI : IsGalois K L :=
    fraction_frobenius_factor
      K n f h hfmonic hfdegree hfactor hfred
  letI : IsIntegralClosure U A L :=
    IsIntegralClosure.of_isIntegrallyClosed U A L
  let G := Gal(L / K)
  letI : MulSemiringAction G U :=
    IsIntegralClosure.MulSemiringAction A K L U
  letI : IsGaloisGroup G A U :=
    IsGaloisGroup.of_isFractionRing G A U K L
  letI : (IsLocalRing.maximalIdeal U).LiesOver
      (IsLocalRing.maximalIdeal A) :=
    (Ideal.liesOver_iff _ _).mpr
      (IsLocalRing.maximalIdeal_comap (algebraMap A U)).symm
  letI : Algebra.IsUnramifiedAt A (IsLocalRing.maximalIdeal U) := by
    change Algebra.FormallyUnramified A
      (Localization.AtPrime (IsLocalRing.maximalIdeal U))
    infer_instance
  let e : G ≃* Gal((U ⧸ IsLocalRing.maximalIdeal U) /
      (A ⧸ IsLocalRing.maximalIdeal A)) :=
    Submission.NumberTheory.Milne.galois_unramified_local
      (R := A) (S := U) (G := G)
      (IsLocalRing.maximalIdeal A)
      (IsDiscreteValuationRing.not_a_field A)
      (IsDiscreteValuationRing.not_a_field U)
  let kU := IsLocalRing.ResidueField U
  letI : Fintype k := Fintype.ofFinite k
  letI : Module.Finite k kU := Module.finite_of_finrank_pos (by
    rw [hresdegree]
    exact NeZero.pos n)
  letI : Finite kU := Module.finite_of_finite k
  letI : Finite (A ⧸ IsLocalRing.maximalIdeal A) := by
    change Finite k
    infer_instance
  letI : Fintype (A ⧸ IsLocalRing.maximalIdeal A) :=
    Fintype.ofFinite _
  letI : Finite (U ⧸ IsLocalRing.maximalIdeal U) := by
    change Finite kU
    infer_instance
  letI : Fintype (U ⧸ IsLocalRing.maximalIdeal U) :=
    Fintype.ofFinite _
  let residueFrob : Gal((U ⧸ IsLocalRing.maximalIdeal U) /
      (A ⧸ IsLocalRing.maximalIdeal A)) :=
    FiniteField.frobeniusAlgEquivOfAlgebraic
      (A ⧸ IsLocalRing.maximalIdeal A)
      (U ⧸ IsLocalRing.maximalIdeal U)
  let φ : G := e.symm residueFrob
  have hcyclicResidue : IsCyclic Gal((U ⧸ IsLocalRing.maximalIdeal U) /
      (A ⧸ IsLocalRing.maximalIdeal A)) := by
    change IsCyclic Gal(kU / k)
    infer_instance
  have hcyclic : IsCyclic G := e.isCyclic.mpr hcyclicResidue
  refine ⟨hcyclic, φ, ?_, ?_⟩
  · calc
      orderOf φ = orderOf residueFrob := e.symm.orderOf_eq residueFrob
      _ = Module.finrank (A ⧸ IsLocalRing.maximalIdeal A)
          (U ⧸ IsLocalRing.maximalIdeal U) :=
        FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic
          (A ⧸ IsLocalRing.maximalIdeal A)
          (U ⧸ IsLocalRing.maximalIdeal U)
      _ = n := hresdegree
  · intro σ
    obtain ⟨i, hipow⟩ :=
      (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (A ⧸ IsLocalRing.maximalIdeal A)
        (U ⧸ IsLocalRing.maximalIdeal U)).surjective (e σ)
    refine ⟨i.1, ?_, ?_⟩
    · have hdegq :
          Module.finrank (A ⧸ IsLocalRing.maximalIdeal A)
            (U ⧸ IsLocalRing.maximalIdeal U) = n := hresdegree
      rw [← hdegq]
      exact i.2
    · change (e.symm residueFrob) ^ i.1 = σ
      apply e.injective
      calc
        e ((e.symm residueFrob) ^ i.1) = residueFrob ^ i.1 := by
          rw [map_pow, e.apply_symm_apply]
        _ = e σ := hipow

/-- For every positive `n`, there is a degree-`n` unramified Galois
extension of `K` whose Galois group is cyclic and generated by arithmetic
Frobenius.  The extension is presented as the fraction field of an
unramified discrete valuation ring over `Valued.integer K`. -/
theorem unramified_galois_extension (n : ℕ) [NeZero n] :
    let q := Nat.card (kK K)
    ∃ f h : (OK K)[X],
      f.Monic ∧ h.Monic ∧
        X ^ q ^ n - X = f * h ∧
        f.natDegree = n ∧
        Irreducible (f.map (IsLocalRing.residue (OK K))) ∧
        (f.map (IsLocalRing.residue (OK K))).Separable ∧
        let U := AdjoinRoot f
        ∃ hfirr : Irreducible f,
          ∃ hfmonic' : f.Monic,
            letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
            ∃ hlocal : IsLocalRing U,
              letI := hlocal
              IsDiscreteValuationRing U ∧
                Algebra.FormallyUnramified (OK K) U ∧
                Algebra.IsUnramifiedAt (OK K) (IsLocalRing.maximalIdeal U) ∧
                letI : Algebra K (FractionRing U) :=
                  frobeniusFractionAlgebra K hfmonic' hfirr
                Module.finrank K (FractionRing U) = n ∧
                  IsGalois K (FractionRing U) ∧
                  IsCyclic Gal(FractionRing U / K) ∧
                  ∃ φ : Gal(FractionRing U / K),
                    orderOf φ = n ∧ ∀ σ : Gal(FractionRing U / K),
                      ∃ i < n, φ ^ i = σ := by
  obtain ⟨f, h, hfmonic, hhmonic, hfactor, hfdegree, hfred, hfsep⟩ :=
    frobenius_hensel_factor K n
  let A := OK K
  let U := AdjoinRoot f
  have hfirr : Irreducible f :=
    hfmonic.irreducible_of_irreducible_map (IsLocalRing.residue A) f hfred
  letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
  letI : FaithfulSMul A U :=
    (faithfulSMul_iff_algebraMap_injective A U).2
      (adjoin_root_injective K hfmonic hfirr)
  let hlocal : IsLocalRing U :=
    adjoin_ring_irreducible
      A f hfmonic hfred
  letI : IsLocalRing U := hlocal
  letI : Module.Finite A U := hfmonic.finite_adjoinRoot
  letI : Algebra.IsIntegral A U := Algebra.IsIntegral.of_finite A U
  letI : Algebra.FormallyUnramified A U :=
    formally_irreducible_separable
      A f hfmonic hfred hfsep
  letI : IsDedekindDomain U := isDedekindDomain.of_formallyUnramified A U
  have hnfield : ¬ IsField U := by
    intro hU
    exact IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField
        (FaithfulSMul.algebraMap_injective A U) hU)
  have hdvr : IsDiscreteValuationRing U :=
    ((IsDiscreteValuationRing.TFAE U hnfield).out 2 0).mp
      (inferInstance : IsDedekindDomain U)
  letI : Algebra K (FractionRing U) :=
    frobeniusFractionAlgebra K hfmonic hfirr
  have hdegree : Module.finrank K (FractionRing U) = n := by
    let uFracAlgebra : Algebra U (FractionRing U) := OreLocalization.instAlgebra
    letI : SMul U (FractionRing U) := uFracAlgebra.toSMul
    letI : Algebra U (FractionRing U) := uFracAlgebra
    let aFracAlgebra : Algebra A (FractionRing U) :=
      ((algebraMap U (FractionRing U)).comp (algebraMap A U)).toAlgebra
    letI : SMul A (FractionRing U) := aFracAlgebra.toSMul
    letI : Algebra A (FractionRing U) := aFracAlgebra
    letI : FaithfulSMul A (FractionRing U) :=
      (faithfulSMul_iff_algebraMap_injective A (FractionRing U)).2 <| by
        change Function.Injective
          ((algebraMap U (FractionRing U)).comp (algebraMap A U))
        exact (IsFractionRing.injective U (FractionRing U)).comp
          (FaithfulSMul.algebraMap_injective A U)
    letI : IsScalarTower A U (FractionRing U) :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower A K (FractionRing U) :=
      IsScalarTower.of_algebraMap_eq' (by
        ext x
        change algebraMap A (FractionRing U) x =
          algebraMap K (FractionRing U) (algebraMap A K x)
        exact IsFractionRing.lift_algebraMap
          (FaithfulSMul.algebraMap_injective A (FractionRing U)) x |>.symm)
    calc
      Module.finrank K (FractionRing U) = Module.finrank A U :=
        Algebra.IsAlgebraic.finrank_of_isFractionRing A K U (FractionRing U)
      _ = f.natDegree := (AdjoinRoot.powerBasis' hfmonic).finrank
      _ = n := hfdegree
  have hgalois : IsGalois K (FractionRing U) :=
    fraction_frobenius_factor
      K n f h hfmonic hfdegree hfactor hfred
  obtain ⟨hcyclic, φ, hφorder, hφgen⟩ :=
    frobenius_generator_factor
      K n f h hfmonic hfdegree hfactor hfred
  refine ⟨f, h, hfmonic, hhmonic, hfactor, hfdegree, hfred, hfsep,
    hfirr, hfmonic, hlocal, hdvr, inferInstance, ?_, hdegree, hgalois, hcyclic,
    φ, hφorder, hφgen⟩
  change Algebra.FormallyUnramified A
    (Localization.AtPrime (IsLocalRing.maximalIdeal U))
  infer_instance

/-- Every positive integer occurs as the degree of a cyclic Galois extension
of `K`.  This packages the unramified construction without exposing its
presentation by a Hensel-lifted polynomial. -/
theorem cyclic_galois_extension (n : ℕ) [NeZero n] :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L)
      (_ : Module.Finite K L) (_ : IsGalois K L),
      Module.finrank K L = n ∧
        IsCyclic Gal(L / K) ∧
        ((X ^ (Nat.card 𝓀[K]) ^ n - X : K[X]).map
          (algebraMap K L)).Splits ∧
        (∃ φ : Gal(L / K), orderOf φ = n) ∧
        ∃ α : L,
          ((X ^ (Nat.card 𝓀[K]) ^ n - X : K[X]).map
            (algebraMap K L)).IsRoot α ∧
          (minpoly K α).natDegree = n := by
  obtain ⟨f, h, hfmonic, hhmonic, hfactor, hfdegree, hfred, hfsep,
      hfirr, hfmonic', hlocal, hdvr, hunramified, hunramifiedAt,
      hdegree, hgalois, hcyclic, φ, hφorder, hφgen⟩ :=
    unramified_galois_extension K n
  let U := AdjoinRoot f
  letI : IsDomain U := AdjoinRoot.isDomain_of_prime hfirr.prime
  letI : IsLocalRing U := hlocal
  let L := FractionRing U
  letI : Algebra K L := frobeniusFractionAlgebra K hfmonic' hfirr
  letI : Module.Finite K L := Module.finite_of_finrank_pos (by
    rw [hdegree]
    exact NeZero.pos n)
  letI : IsGalois K L := hgalois
  have hfullSplit :=
    frobenius_splits_fraction
      K n f hfmonic hfdegree hfred
  let A := OK K
  let uFracAlgebra : Algebra U L := OreLocalization.instAlgebra
  letI : SMul U L := uFracAlgebra.toSMul
  letI : Algebra U L := uFracAlgebra
  let aFracAlgebra : Algebra A L :=
    ((algebraMap U L).comp (algebraMap A U)).toAlgebra
  letI : SMul A L := aFracAlgebra.toSMul
  letI : Algebra A L := aFracAlgebra
  letI : FaithfulSMul A L :=
    (faithfulSMul_iff_algebraMap_injective A L).2 <| by
      change Function.Injective
        ((algebraMap U L).comp (algebraMap A U))
      exact (IsFractionRing.injective U L).comp
        (adjoin_root_injective K hfmonic hfirr)
  letI : IsScalarTower A U L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' (by
    ext x
    change algebraMap A L x = algebraMap K L (algebraMap A K x)
    exact IsFractionRing.lift_algebraMap
      (FaithfulSMul.algebraMap_injective A L) x |>.symm)
  let fK : K[X] := f.map (algebraMap A K)
  have hfKirred : Irreducible fK :=
    (hfmonic.irreducible_iff_irreducible_map_fraction_map).mp hfirr
  let alpha : U := AdjoinRoot.root f
  let alphaL : L := algebraMap U L alpha
  have halphaRoot : (f.map (algebraMap A U)).IsRoot alpha :=
    AdjoinRoot.isRoot_root f
  have hmaps :
      (algebraMap K L).comp (algebraMap A K) =
        (algebraMap U L).comp (algebraMap A U) :=
    (IsScalarTower.algebraMap_eq A K L).symm.trans
      (IsScalarTower.algebraMap_eq A U L)
  have halphaLRoot : aeval alphaL fK = 0 := by
    rw [IsRoot, eval_map] at halphaRoot
    have hx := congrArg (algebraMap U L) halphaRoot
    rw [map_zero] at hx
    simpa [fK, alphaL] using
      (map_aeval_eq_aeval_map hmaps f alpha).symm.trans hx
  have hminpoly : minpoly K alphaL = fK :=
    (minpoly.eq_of_irreducible_of_monic hfKirred halphaLRoot
      (hfmonic.map (algebraMap A K))).symm
  have hfactorL :
      (((X ^ (Nat.card (kK K)) ^ n - X : A[X]).map
        (algebraMap A K)).map (algebraMap K L)) =
      (f.map (algebraMap A K)).map (algebraMap K L) *
        (h.map (algebraMap A K)).map (algebraMap K L) := by
    have hx := congrArg
      (Polynomial.map ((algebraMap K L).comp (algebraMap A K))) hfactor
    simpa [map_map] using hx
  have halphaFullNorm :
      (((X ^ (Nat.card (kK K)) ^ n - X : A[X]).map
        (algebraMap A K)).map (algebraMap K L)).IsRoot alphaL := by
    rw [hfactorL, IsRoot, eval_mul]
    have hfzero :
        ((f.map (algebraMap A K)).map
          (algebraMap K L)).eval alphaL = 0 := by
      simpa [fK, aeval_def] using halphaLRoot
    rw [hfzero, zero_mul]
  have hcard : Nat.card (kK K) = Nat.card 𝓀[K] := rfl
  have halphaFull :
      ((X ^ (Nat.card 𝓀[K]) ^ n - X : K[X]).map
        (algebraMap K L)).IsRoot alphaL := by
    rw [← hcard]
    simpa using halphaFullNorm
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance,
    hdegree, hcyclic, hfullSplit, ⟨φ, hφorder⟩, alphaL, halphaFull, by
      rw [hminpoly]
      simpa [fK] using
        (hfmonic.natDegree_map (algebraMap A K)).trans hfdegree⟩

end

end Submission.CField.LBrauer

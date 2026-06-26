import Towers.ClassField.LocalGlobalPowers.CompletionSplitting
import Towers.ClassField.LocalGlobalPowers.RadicalExtension
import Towers.ClassField.HilbertSymbols.KummerPowerInflation

/-!
# Cyclic prime-power descent for Theorem VIII.1.4

This is Step 2 of Milne's proof.  It is kept separate because the argument
simultaneously uses factorization, completions, Galois correspondence, and
Proposition VII.4.6.
-/

namespace Towers.CField.LGPowers

open IsDedekindDomain NumberField Polynomial
open Towers.NumberTheory.Milne
open Towers.CField.HSymbol
open Towers.CField.KTheory
open Towers.CField.NIndex

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- Being an `n`th power at every finite place outside a finite set. -/
def AENth
    (K : Type u) [Field K] [NumberField K] (n : ℕ) (a : Kˣ) : Prop :=
  ∃ S : Finset (HeightOneSpectrum (OK K)),
    ∀ P, P ∉ S → ∃ x : P.adicCompletion K,
      x ^ n = algebraMap K (P.adicCompletion K) (a : K)

attribute [local instance] IsCyclic.commGroup

/-- Intermediate fields of a cyclic `p`-extension form a chain. -/
private theorem intermediate_fields_comparable
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E] [IsCyclic Gal(E/F)]
    {p : ℕ} (hp : p.Prime) (hpGroup : IsPGroup p Gal(E/F))
    (K L : IntermediateField F E) : K ≤ L ∨ L ≤ K := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hcard⟩ := (IsPGroup.iff_card (p := p) (G := Gal(E/F))).mp hpGroup
  have subgroup_comparable (H J : Subgroup Gal(E/F)) : H ≤ J ∨ J ≤ H := by
    have hHdiv : Nat.card H ∣ p ^ r := hcard ▸ H.card_subgroup_dvd_card
    have hJdiv : Nat.card J ∣ p ^ r := hcard ▸ J.card_subgroup_dvd_card
    obtain ⟨i, _, hHi⟩ := (Nat.dvd_prime_pow hp).mp hHdiv
    obtain ⟨j, _, hJj⟩ := (Nat.dvd_prime_pow hp).mp hJdiv
    rcases le_total i j with hij | hji
    · left
      have hcardHJ : Nat.card H ∣ Nat.card J := by
        rw [hHi, hJj]
        exact pow_dvd_pow p hij
      let P := (powMonoidHom (Nat.card J) : Gal(E/F) →* Gal(E/F)).ker
      have hJle : J ≤ P := by
        intro x hx
        change x ^ Nat.card J = 1
        exact congrArg Subtype.val
          (pow_card_eq_one' (x := (⟨x, hx⟩ : J)))
      have hPJcard : Nat.card P = Nat.card J := by
        rw [IsCyclic.card_powMonoidHom_ker]
        exact Nat.gcd_eq_right J.card_subgroup_dvd_card
      have hJP : J = P :=
        Subgroup.eq_of_le_of_card_ge hJle (by rw [hPJcard])
      rw [hJP]
      intro x hx
      change x ^ Nat.card J = 1
      obtain ⟨d, hd⟩ := hcardHJ
      have hpow : x ^ Nat.card H = 1 :=
        congrArg Subtype.val
          (pow_card_eq_one' (x := (⟨x, hx⟩ : H)))
      rw [hd, pow_mul, hpow, one_pow]
    · right
      have hcardJH : Nat.card J ∣ Nat.card H := by
        rw [hHi, hJj]
        exact pow_dvd_pow p hji
      let P := (powMonoidHom (Nat.card H) : Gal(E/F) →* Gal(E/F)).ker
      have hHle : H ≤ P := by
        intro x hx
        change x ^ Nat.card H = 1
        exact congrArg Subtype.val
          (pow_card_eq_one' (x := (⟨x, hx⟩ : H)))
      have hPHcard : Nat.card P = Nat.card H := by
        rw [IsCyclic.card_powMonoidHom_ker]
        exact Nat.gcd_eq_right H.card_subgroup_dvd_card
      have hHP : H = P :=
        Subgroup.eq_of_le_of_card_ge hHle (by rw [hPHcard])
      rw [hHP]
      intro x hx
      change x ^ Nat.card H = 1
      obtain ⟨d, hd⟩ := hcardJH
      have hpow : x ^ Nat.card J = 1 :=
        congrArg Subtype.val
          (pow_card_eq_one' (x := (⟨x, hx⟩ : J)))
      rw [hd, pow_mul, hpow, one_pow]
  rcases subgroup_comparable K.fixingSubgroup L.fixingSubgroup with h | h
  · right
    rw [← IsGalois.fixedField_fixingSubgroup K,
      ← IsGalois.fixedField_fixingSubgroup L]
    exact IntermediateField.fixedField_le h
  · left
    rw [← IsGalois.fixedField_fixingSubgroup K,
      ← IsGalois.fixedField_fixingSubgroup L]
    exact IntermediateField.fixedField_le h

/-- A root after scalar extension is a root of one of the irreducible
factors over the ground field. -/
private theorem factor_root
    {K F : Type*} [Field K] [Field F] (i : K →+* F)
    {f : K[X]} (hf : f ≠ 0) {x : F}
    (hx : (f.map i).IsRoot x) :
    ∃ g : K[X], g ∈ UniqueFactorizationMonoid.factors f ∧
      (g.map i).IsRoot x := by
  classical
  obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hf
  have huunit : IsUnit (eval x ((u : K[X]).map i)) :=
    (u.isUnit.map (mapRingHom i)).map (evalRingHom x)
  have hzero :
      eval x ((UniqueFactorizationMonoid.factors f).prod.map i) = 0 := by
    have hmul :
        eval x (((UniqueFactorizationMonoid.factors f).prod *
          (u : K[X])).map i) = 0 := by
      rw [hu]
      exact hx
    simpa [map_mul, eval_mul, huunit.ne_zero] using hmul
  have hprod :
      ((UniqueFactorizationMonoid.factors f).map
        (fun g : K[X] ↦ eval x (g.map i))).prod = 0 := by
    calc
      _ = (((UniqueFactorizationMonoid.factors f).map (map i)).map
          (eval x)).prod := by
        simp only [Multiset.map_map, Function.comp_apply]
      _ = eval x
          (((UniqueFactorizationMonoid.factors f).map (map i)).prod) :=
        (eval_multiset_prod _ _).symm
      _ = eval x
          ((UniqueFactorizationMonoid.factors f).prod.map i) := by
        rw [Polynomial.map_multiset_prod]
      _ = 0 := hzero
  have hmemzero : (0 : F) ∈
      (UniqueFactorizationMonoid.factors f).map
        (fun g : K[X] ↦ eval x (g.map i)) :=
    Multiset.prod_eq_zero_iff.mp hprod
  obtain ⟨g, hg, hgzero⟩ := Multiset.mem_map.mp hmemzero
  exact ⟨g, hg, by simp [IsRoot, hgzero]⟩

set_option synthInstance.maxHeartbeats 500000 in
-- The cyclotomic descent proof combines several large finite-extension instance towers.
set_option maxHeartbeats 5000000 in
/-- Step 2 of Milne's proof: descent from a cyclic cyclotomic
`p`-extension.  The power in the cyclotomic field is the output of Theorem
1.1 after base change. -/
theorem cyclic_p_cyclotomic
    (h46 : NontrivialNonsplitPrimes.{u})
    (p r : ℕ) (hp : p.Prime)
    (K C : Type u) [Field K] [NumberField K]
    [Field C] [NumberField C] [Algebra K C]
    [FiniteDimensional K C] [IsGalois K C]
    [IsCyclotomicExtension {p ^ r} K C]
    [IsCyclic Gal(C/K)]
    (hpGroup : IsPGroup p Gal(C/K))
    (a : Kˣ) (hlocal : AENth K (p ^ r) a)
    (hpowerC : Units.map (algebraMap K C) a ∈
      (powMonoidHom (p ^ r) : Cˣ →* Cˣ).range) :
    a ∈ (powMonoidHom (p ^ r) : Kˣ →* Kˣ).range := by
  classical
  let n := p ^ r
  have hn : 0 < n := pow_pos hp.pos r
  letI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨beta, hbeta⟩ := hpowerC
  have hbeta' : (beta : C) ^ n = algebraMap K C (a : K) := by
    simpa using congrArg Units.val hbeta
  let f : K[X] := X ^ n - Polynomial.C (a : K)
  have hf0 : f ≠ 0 := (monic_X_pow_sub_C (a : K) hn.ne').ne_zero
  have hfnotunit : ¬IsUnit f := by
    intro hunit
    have hdeg0 := natDegree_eq_zero_of_isUnit hunit
    rw [natDegree_X_pow_sub_C] at hdeg0
    omega
  have hsplit : (f.map (algebraMap K C)).Splits := by
    let zeta := IsCyclotomicExtension.zeta n K C
    have hzeta : IsPrimitiveRoot zeta n :=
      IsCyclotomicExtension.zeta_spec n K C
    simpa [f] using radical_splits_root hzeta hbeta'
  let fac : Finset K[X] :=
    (UniqueFactorizationMonoid.factors f).toFinset
  have hfac : fac.Nonempty := by
    obtain ⟨g, hg⟩ :=
      UniqueFactorizationMonoid.exists_mem_factors hf0 hfnotunit
    exact ⟨g, Multiset.mem_toFinset.mpr hg⟩
  let Fac := ↑fac
  have root_exists (g : Fac) :
      ∃ alpha : C, (g.1.map (algebraMap K C)).IsRoot alpha := by
    have hgmem : g.1 ∈ UniqueFactorizationMonoid.factors f :=
      Multiset.mem_toFinset.mp g.2
    have hgirr : Irreducible g.1 :=
      UniqueFactorizationMonoid.irreducible_of_factor g.1 hgmem
    have hgdiv : g.1 ∣ f :=
      UniqueFactorizationMonoid.dvd_of_mem_factors hgmem
    have hgmap0 : g.1.map (algebraMap K C) ≠ 0 := by
      intro hzero
      exact hgirr.ne_zero
        ((Polynomial.map_eq_zero_iff (algebraMap K C).injective).mp hzero)
    have hmapf0 : f.map (algebraMap K C) ≠ 0 := by
      intro hzero
      exact hf0
        ((Polynomial.map_eq_zero_iff (algebraMap K C).injective).mp hzero)
    have hgsplit : (g.1.map (algebraMap K C)).Splits :=
      hsplit.of_dvd hmapf0 (Polynomial.map_dvd _ hgdiv)
    obtain ⟨alpha, halpha⟩ := hgsplit.exists_eval_eq_zero
      (by
        rw [degree_map]
        exact ne_of_gt hgirr.degree_pos)
    exact ⟨alpha, halpha⟩
  let alpha : Fac → C := fun g ↦ (root_exists g).choose
  have halpha (g : Fac) :
      (g.1.map (algebraMap K C)).IsRoot (alpha g) :=
    (root_exists g).choose_spec
  let E : Fac → IntermediateField K C := fun g ↦
    IntermediateField.adjoin K {alpha g}
  let degree : Fac → ℕ := fun g ↦ Module.finrank K (E g)
  have hFacNonempty : (Finset.univ : Finset Fac).Nonempty := by
    obtain ⟨g, hg⟩ := hfac
    exact ⟨⟨g, hg⟩, Finset.mem_univ _⟩
  obtain ⟨g₀, _, hg₀min⟩ :=
    (Finset.univ : Finset Fac).exists_min_image degree hFacNonempty
  let E₀ := E g₀
  have hE₀le (g : Fac) : E₀ ≤ E g := by
    rcases intermediate_fields_comparable hp hpGroup E₀ (E g) with h | h
    · exact h
    · have hdegree : Module.finrank K E₀ ≤ Module.finrank K (E g) :=
        hg₀min g (Finset.mem_univ g)
      exact (IntermediateField.eq_of_le_of_finrank_le h hdegree).symm.le
  letI : FiniteDimensional ℚ E₀ := FiniteDimensional.trans ℚ K E₀
  letI : NumberField E₀ := {}
  obtain ⟨S, hS⟩ := hlocal
  have hsplitOutside : ∀ P : HeightOneSpectrum (OK K), P ∉ S →
      SplitsCompletelyAt K E₀ P := by
    intro P hP
    obtain ⟨x, hx⟩ := hS P hP
    have hxroot : (f.map (algebraMap K (P.adicCompletion K))).IsRoot x := by
      simpa [f, IsRoot, sub_eq_zero] using hx
    obtain ⟨g, hgfac, hgroot⟩ :=
      factor_root
        (algebraMap K (P.adicCompletion K)) hf0 hxroot
    let gg : Fac :=
      ⟨g, Multiset.mem_toFinset.mpr hgfac⟩
    have hgeval : aeval (alpha gg) g = 0 := by
      simpa [Polynomial.IsRoot, aeval_def] using halpha gg
    have hgirr : Irreducible g :=
      UniqueFactorizationMonoid.irreducible_of_factor g hgfac
    have hmin : g * Polynomial.C g.leadingCoeff⁻¹ =
        minpoly K (alpha gg) :=
      minpoly.eq_of_irreducible hgirr hgeval
    have hminroot : ((minpoly K (alpha gg)).map
        (algebraMap K (P.adicCompletion K))).IsRoot x := by
      rw [← hmin, Polynomial.map_mul, Polynomial.IsRoot,
        eval_mul, hgroot, zero_mul]
    letI : FiniteDimensional ℚ (E gg) :=
      FiniteDimensional.trans ℚ K (E gg)
    letI : NumberField (E gg) := {}
    have hsplitg : SplitsCompletelyAt K (E gg) P :=
      splits_completely_minpoly
        K C (alpha gg) P x hminroot
    have hle : E₀ ≤ E gg := hE₀le gg
    letI : Algebra E₀ (E gg) :=
      RingHom.toAlgebra (IntermediateField.inclusion hle)
    letI : IsScalarTower K E₀ (E gg) := by
      refine IsScalarTower.of_algebraMap_eq ?_
      intro z
      apply Subtype.ext
      rfl
    have hnormal₀ : E₀.fixingSubgroup.Normal := inferInstance
    have hnormalg : (E gg).fixingSubgroup.Normal := inferInstance
    letI : IsGalois K E₀ :=
      (InfiniteGalois.normal_iff_isGalois E₀).mp hnormal₀
    letI : IsGalois K (E gg) :=
      (InfiniteGalois.normal_iff_isGalois (E gg)).mp hnormalg
    letI : IsGalois E₀ (E gg) :=
      IsGalois.tower_top_of_isGalois K E₀ (E gg)
    exact splits_completely_tower (E := E₀) P hsplitg
  have hnormal₀ : E₀.fixingSubgroup.Normal := inferInstance
  letI : IsGalois K E₀ :=
    (InfiniteGalois.normal_iff_isGalois E₀).mp hnormal₀
  letI : IsSolvable Gal(C/K) := inferInstance
  letI : IsSolvable Gal(E₀/K) :=
    solvable_of_surjective
      (AlgEquiv.restrictNormalHom_surjective
        (F := K) (K₁ := E₀) (E := C))
  have hdegree₀ : Module.finrank K E₀ = 1 := by
    by_contra hne
    have hinfinite : (splittingPrimes K E₀)ᶜ.Infinite := h46 K E₀ hne
    apply hinfinite
    apply S.finite_toSet.subset
    intro P hPsplit
    by_contra hPS
    exact hPsplit (hsplitOutside P hPS)
  let alpha₀ := alpha g₀
  have halpha₀root : (f.map (algebraMap K C)).IsRoot alpha₀ := by
    have hgdiv : g₀.1 ∣ f :=
      UniqueFactorizationMonoid.dvd_of_mem_factors
        (Multiset.mem_toFinset.mp g₀.2)
    obtain ⟨h, hh⟩ := Polynomial.map_dvd (algebraMap K C) hgdiv
    rw [hh]
    change eval alpha₀
      (g₀.1.map (algebraMap K C) * h) = 0
    rw [eval_mul, halpha g₀, zero_mul]
  have halpha₀pow : alpha₀ ^ n = algebraMap K C (a : K) := by
    simpa [f, IsRoot, sub_eq_zero] using halpha₀root
  let alphaE₀ : E₀ :=
    ⟨alpha₀, IntermediateField.subset_adjoin K {alpha₀}
      (Set.mem_singleton alpha₀)⟩
  obtain ⟨c, hc⟩ :=
    (finrank_eq_one_iff_of_nonzero' (K := K) (1 : E₀) one_ne_zero).mp
      hdegree₀ alphaE₀
  have hc' : algebraMap K C c = alpha₀ := by
    have hcE : algebraMap K E₀ c = alphaE₀ := by
      simpa [Algebra.smul_def] using hc
    exact congrArg Subtype.val hcE
  have hc0 : c ≠ 0 := by
    intro hc0
    have halphaZero : alpha₀ = 0 := by
      rw [← hc', hc0, map_zero]
    have haZero : algebraMap K C (a : K) = 0 := by
      simpa [halphaZero, zero_pow hn.ne'] using halpha₀pow.symm
    exact a.ne_zero ((algebraMap K C).injective
      (haZero.trans (map_zero (algebraMap K C)).symm))
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  change c ^ n = (a : K)
  apply (algebraMap K C).injective
  rw [map_pow, hc', halpha₀pow]

end

end Towers.CField.LGPowers

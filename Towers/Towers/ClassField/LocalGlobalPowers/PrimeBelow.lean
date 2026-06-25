import Towers.ClassField.LocalGlobalPowers.CompletionCompatibility
import Towers.ClassField.HilbertSymbols.KummerPowerInflation
import Towers.ClassField.LocalFields.NormSubgroups
import Towers.NumberTheory.Completions.SemilocalCoordinateAlgebra
import Towers.NumberTheory.Completions.DifferentCompletionConcrete
import Towers.NumberTheory.Cyclotomic.PrimeAutomorphismGroups
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Chapter VIII, Section 1, Theorem 1.4

The Wang-corrected local-to-global power theorem.  The three steps of the
printed proof are kept separate: prime-power reduction, the cyclic
prime-power cyclotomic case, and descent for odd primes by taking norms.
-/

namespace Towers.CField.LGPowers

open IsDedekindDomain NumberField Polynomial
open Towers.CField.LFTheory
open Towers.CField.HSymbol
open Towers.CField.Ideles
open Towers.CField.KTheory
open Towers.CField.ICohomo
open Towers.CField.NIndex

noncomputable section

universe u

private abbrev OK (K : Type u) [Field K] [NumberField K] :=
  NumberField.RingOfIntegers K

/-- Contraction of a finite prime through an extension of number fields. -/
noncomputable def primeBelow
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (Q : HeightOneSpectrum (OK L)) : HeightOneSpectrum (OK K) where
  asIdeal := Q.asIdeal.comap (algebraMap (OK K) (OK L))
  isPrime := Ideal.comap_isPrime (algebraMap (OK K) (OK L)) Q.asIdeal
  ne_bot := Ideal.IsIntegral.comap_ne_bot (OK K) Q.ne_bot

@[simp]
theorem prime_below_ideal
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (Q : HeightOneSpectrum (OK L)) :
    (primeBelow K L Q).asIdeal =
      Q.asIdeal.comap (algebraMap (OK K) (OK L)) := rfl

/-- Only finitely many primes of a finite extension lie over a fixed finite
set of base primes. -/
theorem prime_below_preimage
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (S : Finset (HeightOneSpectrum (OK K))) :
    Set.Finite {Q : HeightOneSpectrum (OK L) | primeBelow K L Q ∈ S} := by
  apply S.finite_toSet.preimage'
  intro P hP
  apply Set.Finite.of_finite_image
      (f := fun Q : HeightOneSpectrum (OK L) ↦ Q.asIdeal)
  · apply (IsDedekindDomain.primesOver_finite P.asIdeal (OK L)).subset
    rintro Q ⟨W, hW, rfl⟩
    exact ⟨W.isPrime, ⟨by
      simpa [primeBelow] using
        (congrArg HeightOneSpectrum.asIdeal hW).symm⟩⟩
  · intro Q hQ Q' hQ' hQQ'
    exact HeightOneSpectrum.ext hQQ'

open Towers.NumberTheory.Milne

/- The completion compatibility proof is compiled in
`Theorem14CompletionCompatibility`. -/
/-

set_option synthInstance.maxHeartbeats 500000 in
set_option maxHeartbeats 5000000 in
set_option maxRecDepth 100000 in
/-- The semilocal coordinate map between completed fields agrees with the
two global embeddings on the ground field. -/
theorem adic_global_compatibility
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    (P : HeightOneSpectrum (OK K))
    (hP : P.asIdeal.map (algebraMap (OK K) (OK L)) ≠ ⊥)
    (Q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap (OK K) (OK L)))).toFinset)
    (x : K) :
    let E := (factorHeightSpectrum
      (P.asIdeal.map (algebraMap (OK K) (OK L))) Q).adicCompletion L
    letI : Algebra (P.adicCompletion K) E :=
      adicFactorAlgebra (K := K) (L := L) P hP Q
    algebraMap (P.adicCompletion K) E
        (algebraMap K (P.adicCompletion K) x) =
      algebraMap L E (algebraMap K L x) := by
  let R := OK K
  let S := OK L
  let C := P.adicCompletionIntegers K
  let F := P.adicCompletion K
  let V := factorHeightSpectrum
    (P.asIdeal.map (algebraMap R S)) Q
  let B := V.adicCompletionIntegers L
  let E := V.adicCompletion L
  letI : Algebra F E :=
    adicFactorAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C B :=
    adicCompletionAlgebra (K := K) (L := L) P hP Q
  letI : Algebra C E :=
    adicIntegerAlgebra (K := K) (L := L) P hP Q
  let ι := (UniqueFactorizationMonoid.factors
    (P.asIdeal.map (algebraMap R S))).toFinset
  let Bfamily : ι → Type u := fun Q' ↦
    (factorHeightSpectrum
      (P.asIdeal.map (algebraMap R S)) Q').adicCompletionIntegers L
  letI (Q' : ι) : Algebra C (Bfamily Q') :=
    adicCompletionAlgebra
      (K := K) (L := L) P hP Q'
  letI : Algebra C (∀ Q', Bfamily Q') :=
    piIntegersAlgebra
      (K := K) (L := L) P hP
  let e₀ : TensorProduct R C S ≃ₐ[C] (∀ Q', Bfamily Q') :=
    integersPiDifferent
      (K := K) (L := L) P hP
  have hinteger (r : R) :
      algebraMap F E (algebraMap K F (algebraMap R K r)) =
        algebraMap L E (algebraMap K L (algebraMap R K r)) := by
    have hCB : algebraMap C B (algebraMap R C r) =
        algebraMap S B (algebraMap R S r) := by
      calc
        algebraMap C B (algebraMap R C r) =
            e₀ (algebraMap C (TensorProduct R C S) (algebraMap R C r)) Q := by
              exact (congrFun (e₀.commutes (algebraMap R C r)) Q).symm
        _ = e₀ ((1 : C) ⊗ₜ[R] algebraMap R S r) Q := by
              congr 2
              simp
        _ = algebraMap S B (algebraMap R S r) := by
              simpa using
                (pi_different_tmul
                  (K := K) (L := L) P hP (1 : C)
                  (algebraMap R S r) Q)
    calc
      algebraMap F E (algebraMap K F (algebraMap R K r)) =
          algebraMap F E (algebraMap C F (algebraMap R C r)) := by
            rw [IsScalarTower.algebraMap_apply R K F,
              IsScalarTower.algebraMap_apply R C F]
      _ = algebraMap C E (algebraMap R C r) := by
            exact (adic_integer_algebra
              (K := K) (L := L) P hP Q (algebraMap R C r)).symm
      _ = algebraMap B E (algebraMap C B (algebraMap R C r)) := rfl
      _ = algebraMap B E (algebraMap S B (algebraMap R S r)) := by rw [hCB]
      _ = algebraMap L E (algebraMap S L (algebraMap R S r)) := by
            rw [IsScalarTower.algebraMap_apply S B E,
              IsScalarTower.algebraMap_apply S L E]
      _ = algebraMap L E (algebraMap K L (algebraMap R K r)) := by
            congr 1
            exact IsScalarTower.algebraMap_apply R K L r
  change algebraMap F E (algebraMap K F x) =
    algebraMap L E (algebraMap K L x)
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R x
  rw [← hab]
  simp only [map_div₀]
  rw [hinteger a, hinteger b]

-/

set_option synthInstance.maxHeartbeats 100000 in
-- Transporting almost-everywhere power data through all completed primes is instance-heavy.
set_option maxHeartbeats 2000000 in
set_option maxRecDepth 100000 in
/-- Almost-everywhere local powers remain local powers after a finite base
extension. -/
theorem AENth.map
    {K L : Type u} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]
    {n : ℕ} {a : Kˣ}
    (h : AENth K n a) :
    AENth L n (Units.map (algebraMap K L) a) := by
  classical
  obtain ⟨S, hS⟩ := h
  let T : Finset (HeightOneSpectrum (OK L)) :=
    (prime_below_preimage K L S).toFinset
  refine ⟨T, ?_⟩
  intro Q hQ
  have hbelow : primeBelow K L Q ∉ S := by
    intro hmem
    apply hQ
    change Q ∈ (prime_below_preimage K L S).toFinset
    rw [Set.Finite.mem_toFinset]
    exact hmem
  let P := primeBelow K L Q
  obtain ⟨x, hx⟩ := hS P hbelow
  have hQover : Q.asIdeal.LiesOver P.asIdeal := ⟨rfl⟩
  have hQmem : Q.asIdeal ∈ Ideal.primesOver P.asIdeal (OK L) :=
    ⟨Q.isPrime, hQover⟩
  have hQfactor : Q.asIdeal ∈
      (UniqueFactorizationMonoid.factors
        (P.asIdeal.map (algebraMap (OK K) (OK L)))).toFinset := by
    exact (IsDedekindDomain.mem_primesOverFinset_iff P.ne_bot (OK L)).2 hQmem
  let q : (UniqueFactorizationMonoid.factors
      (P.asIdeal.map (algebraMap (OK K) (OK L)))).toFinset :=
    ⟨Q.asIdeal, hQfactor⟩
  let V := factorHeightSpectrum
    (P.asIdeal.map (algebraMap (OK K) (OK L))) q
  have hVQ : V = Q := by
    apply HeightOneSpectrum.ext
    rfl
  rw [← hVQ]
  have hPmap : P.asIdeal.map (algebraMap (OK K) (OK L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot P.ne_bot
  letI : Algebra (P.adicCompletion K) (V.adicCompletion L) :=
    adicFactorAlgebra
      (K := K) (L := L) P hPmap q
  refine ⟨algebraMap (P.adicCompletion K) (V.adicCompletion L) x, ?_⟩
  calc
    algebraMap (P.adicCompletion K) (V.adicCompletion L) x ^ n =
        algebraMap (P.adicCompletion K) (V.adicCompletion L) (x ^ n) := by
          rw [map_pow]
    _ = algebraMap (P.adicCompletion K) (V.adicCompletion L)
        (algebraMap K (P.adicCompletion K) (a : K)) := by rw [hx]
    _ = algebraMap L (V.adicCompletion L)
        (algebraMap K L (a : K)) :=
      adic_global_compatibility
        P hPmap q (a : K)
    _ = algebraMap L (V.adicCompletion L)
        ((Units.map (algebraMap K L) a : Lˣ) : L) := by rfl

/-- A local `n`th power is locally an `m`th power whenever `m ∣ n`. -/
theorem AENth.of_dvd
    {K : Type u} [Field K] [NumberField K]
    {m n : ℕ} {a : Kˣ} (hmn : m ∣ n)
    (h : AENth K n a) :
    AENth K m a := by
  obtain ⟨d, rfl⟩ := hmn
  obtain ⟨S, hS⟩ := h
  refine ⟨S, ?_⟩
  intro P hP
  obtain ⟨x, hx⟩ := hS P hP
  refine ⟨x ^ d, ?_⟩
  calc
    (x ^ d) ^ m = x ^ (d * m) := by rw [pow_mul]
    _ = x ^ (m * d) := by rw [Nat.mul_comm]
    _ = algebraMap K (P.adicCompletion K) (a : K) := hx

/-- The exact cyclotomic hypothesis in Theorem 1.4.  The conductor is the
largest power of two dividing `n`. -/
def CyclicPrimaryExtension
    (K : Type u) [Field K] [NumberField K] (n : ℕ) : Prop :=
  ∃ (C : Type u) (_ : Field C) (_ : NumberField C)
    (_ : Algebra K C) (_ : FiniteDimensional K C)
    (_ : IsGalois K C)
    (_ : IsCyclotomicExtension {2 ^ n.factorization 2} K C),
    IsCyclic Gal(C/K)

/-- Milne's norm argument in Step 3.  If an element becomes a `p ^ r`-th
power after a finite extension whose degree is prime to `p`, it was already
a `p ^ r`-th power in the ground field. -/
theorem after_coprime_finrank
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {p r : ℕ}
    (hdegree : (Module.finrank K L).Coprime p) (a : Kˣ)
    (hpower : Units.map (algebraMap K L) a ∈
      (powMonoidHom (p ^ r) : Lˣ →* Lˣ).range) :
    a ∈ (powMonoidHom (p ^ r) : Kˣ →* Kˣ).range := by
  obtain ⟨b, hb⟩ := hpower
  have hnormMap : normOnUnits K L (Units.map (algebraMap K L) a) =
      a ^ Module.finrank K L := by
    apply Units.ext
    exact Algebra.norm_algebraMap (R := K) (S := L) (a : K)
  have hnormPower : normOnUnits K L b ^ (p ^ r) =
      a ^ Module.finrank K L := by
    rw [← hnormMap, ← hb]
    exact (map_pow (normOnUnits K L) b (p ^ r)).symm
  have hclassPower : (powerClass (p ^ r) a) ^ Module.finrank K L = 1 := by
    rw [← map_pow]
    apply (power_class_nth (p ^ r)
      (a ^ Module.finrank K L)).2
    exact ⟨normOnUnits K L b, hnormPower⟩
  have hclass : powerClass (p ^ r) a = 1 :=
    power_class_coprime hdegree
      (powerClass (p ^ r) a) hclassPower
  exact (power_class_nth (p ^ r) a).1 hclass

/- The cyclic descent and its completion lemmas now live in the two helper
modules imported above.  The old in-file copy is retained temporarily in
this nested comment to keep the mathematical derivation visible while the
source statement below uses the compiled declarations. -/
/-

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
        eval x (((UniqueFactorizationMonoid.factors f).prod * (u : K[X])).map i) = 0 := by
      rw [hu]
      exact hx
    simpa [map_mul, eval_mul, huunit.ne_zero] using hmul
  have hprod :
      ((UniqueFactorizationMonoid.factors f).map
        (fun g : K[X] ↦ eval x (g.map i))).prod = 0 := by
    simpa using hzero
  have hmemzero : (0 : F) ∈
      (UniqueFactorizationMonoid.factors f).map
        (fun g : K[X] ↦ eval x (g.map i)) :=
    Multiset.prod_eq_zero_iff.mp hprod
  obtain ⟨g, hg, hgzero⟩ := Multiset.mem_map.mp hmemzero
  exact ⟨g, hg, by simpa [IsRoot, hgzero]⟩

set_option synthInstance.maxHeartbeats 500000 in
-- The two-primary cyclotomic reduction builds a large tower of local-field instances.
set_option maxHeartbeats 3000000 in
/-- In a finite Galois extension, one degree-one completed factor already
implies complete splitting. -/
private theorem splits_completely_finrank
    (K L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : HeightOneSpectrum (OK K))
    (w : CompletionPlacesAbove (L := L) (FinitePlace.mk p).val)
    (hlocal :
      letI : Algebra (FinitePlace.mk p).val.Completion w.1.Completion :=
        (completionLies (FinitePlace.mk p).val w.1 w.2).toAlgebra
      Module.finrank (FinitePlace.mk p).val.Completion w.1.Completion = 1) :
    SplitsCompletelyAt K L p := by
  let v := (FinitePlace.mk p).val
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial p⟩
  letI : IsUltrametricDist v.Completion :=
    placeUltrametricDist p
  have hw : w.1.IsNontrivial := absolute_extension_nontrivial v w
  have hwna : IsNonarchimedean w.1 :=
    absolute_extension_nonarchimedean v w
  let Q := nonarchimedeanHeightSpectrum w.1 hw hwna
  letI : Q.asIdeal.LiesOver p.asIdeal :=
    nonarchimedean_spectrum_lies p w.1 w.2 hw hwna
  letI : Algebra v.Completion w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  letI : MulSemiringAction Gal(L/K) (OK L) :=
    IsIntegralClosure.MulSemiringAction (OK K) K L (OK L)
  letI : MulSemiringAction Gal(L/K) (Ideal (OK L)) :=
    Ideal.pointwiseMulSemiringAction
  letI : IsGaloisGroup Gal(L/K) (OK K) (OK L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (OK K) (OK L) K L
  letI : p.asIdeal.IsMaximal := p.isMaximal
  letI : Q.asIdeal.IsMaximal := Q.isMaximal
  letI : Field (OK K ⧸ p.asIdeal) := Ideal.Quotient.field p.asIdeal
  letI : Field (OK L ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  letI : Finite (OK K ⧸ p.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient p.ne_bot
  letI : Finite (OK L ⧸ Q.asIdeal) :=
    Ring.HasFiniteQuotients.finiteQuotient Q.ne_bot
  letI : Algebra.IsSeparable (OK K ⧸ p.asIdeal) (OK L ⧸ Q.asIdeal) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hstabilizer :
      Nat.card (MulAction.stabilizer Gal(L/K) Q.asIdeal) = 1 := by
    calc
      Nat.card (MulAction.stabilizer Gal(L/K) Q.asIdeal) =
          Nat.card (absoluteValueDecomposition v w.1) := by
        rw [centered_stabilizer_decomposition v w.1 hw hwna]
      _ = Module.finrank v.Completion w.1.Completion := by
        rw [finrank_decomposition_card p w]
      _ = 1 := hlocal
  have hQmem : Q.asIdeal ∈ Ideal.primesOver p.asIdeal (OK L) :=
    ⟨Q.isPrime, inferInstance⟩
  apply (splits_completely_bot p Q.asIdeal hQmem).mpr
  exact (MulAction.stabilizer Gal(L/K) Q.asIdeal).eq_bot_of_card_eq hstabilizer

set_option synthInstance.maxHeartbeats 500000 in
set_option maxHeartbeats 3000000 in
/-- If an irreducible factor has a local root, the field generated by any
of its roots inside a cyclic Galois extension splits completely there. -/
private theorem splits_completely_minpoly
    (K C : Type u) [Field K] [NumberField K]
    [Field C] [NumberField C] [Algebra K C]
    [FiniteDimensional K C] [IsGalois K C] [IsCyclic Gal(C/K)]
    (alpha : C) (P : HeightOneSpectrum (OK K))
    (x : P.adicCompletion K)
    (hx : ((minpoly K alpha).map
      (algebraMap K (P.adicCompletion K))).IsRoot x) :
    SplitsCompletelyAt K (IntermediateField.adjoin K {alpha}) P := by
  let E : IntermediateField K C := IntermediateField.adjoin K {alpha}
  let alphaE : E :=
    ⟨alpha, IntermediateField.subset_adjoin K {alpha}
      (Set.mem_singleton alpha)⟩
  have hgen : IntermediateField.adjoin K {alphaE} = ⊤ := by
    apply IntermediateField.map_injective E.val
    rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map,
      IntermediateField.fieldRange_val]
    change IntermediateField.adjoin K (Subtype.val '' {alphaE}) = E
    simp [E, alphaE]
  letI : FiniteDimensional K E := inferInstance
  letI : FiniteDimensional ℚ E := FiniteDimensional.trans ℚ K E
  letI : NumberField E := {}
  have hnormal : E.fixingSubgroup.Normal := inferInstance
  letI : IsGalois K E :=
    (InfiniteGalois.normal_iff_isGalois E).mp hnormal
  let v := (FinitePlace.mk P).val
  let F := v.Completion
  letI : Fact v.IsNontrivial :=
    ⟨absolute_value_nontrivial P⟩
  letI : IsUltrametricDist F :=
    placeUltrametricDist P
  let eP : F ≃+* P.adicCompletion K :=
    placeCompletionAdic P
  let xF : F := eP.symm x
  have hcomp : eP.toRingHom.comp (completionEmbedding v) =
      algebraMap K (P.adicCompletion K) := by
    ext z
    exact finite_place_adic P z
  have hxF : ((minpoly K alphaE).map (completionEmbedding v)).IsRoot xF := by
    have hmin : minpoly K alphaE = minpoly K alpha :=
      (minpoly.algHom_eq E.val E.val.injective alphaE).symm
    rw [hmin]
    change eval₂ (completionEmbedding v) xF (minpoly K alpha) = 0
    apply eP.injective
    rw [map_zero, hom_eval₂, eP.apply_symm_apply, hcomp]
    exact hx
  let g : F[X] := X - Polynomial.C xF
  have hgdiv : g ∣ (minpoly K alphaE).map (completionEmbedding v) :=
    dvd_iff_isRoot.mpr hxF
  let G : CompletedMinpolyFactor v alphaE :=
    ⟨g, irreducible_X_sub_C xF, monic_X_sub_C xF, hgdiv⟩
  let w : CompletionPlacesAbove (L := E) v :=
    completedMinpolyExtension v alphaE hgen G
  letI : Algebra F w.1.Completion :=
    (completionLies v w.1 w.2).toAlgebra
  have hround := congrArg Subtype.val
    (minpoly_place_roundtrip v alphaE hgen G)
  have hminround : minpoly F (completionEmbedding w.1 alphaE) = g := by
    exact hround
  let ew := completionAdjoinMinpoly v alphaE hgen w
  have hdegree : Module.finrank F w.1.Completion = 1 := by
    calc
      Module.finrank F w.1.Completion =
          Module.finrank F
            (AdjoinRoot (minpoly F (completionEmbedding w.1 alphaE))) :=
        ew.toLinearEquiv.finrank_eq.symm
      _ = (minpoly F (completionEmbedding w.1 alphaE)).natDegree := by
        let pbw := AdjoinRoot.powerBasis
          (show minpoly F (completionEmbedding w.1 alphaE) ≠ 0 from
            (minpoly.irreducible
              (IsIntegral.of_finite F (completionEmbedding w.1 alphaE))).ne_zero)
        rw [pbw.finrank, AdjoinRoot.powerBasis_dim]
      _ = g.natDegree := by rw [hminround]
      _ = 1 := natDegree_X_sub_C xF
  exact splits_completely_finrank
    K E P w hdegree

set_option synthInstance.maxHeartbeats 500000 in
-- The odd-primary fixed-field construction requires deeper Galois instance search.
set_option maxHeartbeats 5000000 in
/-- Step 2 of Milne's proof: descent from a cyclic cyclotomic
`p`-extension.  The power in the cyclotomic field is the output of Theorem
1.1 after the base-change lemma above. -/
private theorem cyclic_p_cyclotomic
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
        ((Polynomial.map_injective (algebraMap K C).injective) hzero)
    have hgsplit : (g.1.map (algebraMap K C)).Splits :=
      hsplit.of_dvd (by
        intro hzero
        exact hf0 ((Polynomial.map_injective
          (algebraMap K C).injective) hzero))
        (Polynomial.map_dvd _ hgdiv)
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
      rw [← hmin, map_mul]
      change eval x
        (g.map (algebraMap K (P.adicCompletion K)) *
          (Polynomial.C g.leadingCoeff⁻¹).map
            (algebraMap K (P.adicCompletion K))) = 0
      rw [eval_mul, hgroot, zero_mul]
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
  have hcomm : ∀ sigma tau : Gal(E₀/K), sigma * tau = tau * sigma := by
    intro sigma tau
    obtain ⟨sigma', rfl⟩ := AlgEquiv.restrictNormalHom_surjective E₀ sigma
    obtain ⟨tau', rfl⟩ := AlgEquiv.restrictNormalHom_surjective E₀ tau
    simpa only [map_mul] using
      congrArg (AlgEquiv.restrictNormalHom E₀) (mul_comm sigma' tau')
  letI : IsSolvable Gal(E₀/K) := isSolvable_of_comm hcomm
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
    exact a.ne_zero ((algebraMap K C).injective (by simpa using haZero))
  refine ⟨Units.mk0 c hc0, ?_⟩
  apply Units.ext
  change c ^ n = (a : K)
  apply (algebraMap K C).injective
  rw [map_pow, hc', halpha₀pow]

-/

attribute [local instance] IsCyclic.commGroup

/-- The unit group modulo a power of two is a two-group (cyclicity is not
asserted, and is false in the range relevant to Wang's exception). -/
private theorem zmod_units_p (r : ℕ) :
    IsPGroup 2 (ZMod (2 ^ r))ˣ := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  cases r with
  | zero =>
      exact IsPGroup.of_card (n := 0) (by simp)
  | succ s =>
      exact IsPGroup.of_card (n := s) (by
        rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
          Nat.totient_prime_pow_succ Nat.prime_two]
        norm_num)

/-- For a prime `p`, the units congruent to one modulo `p` inside
`(Z/p^rZ)ˣ` form a `p`-group. -/
private theorem zmod_units_group
    (p r : ℕ) (hp : p.Prime) (hr : 0 < r) :
    IsPGroup p (ZMod.unitsMap
      (show p ∣ p ^ r from dvd_pow_self p hr.ne')).ker := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  let hdiv : p ∣ p ^ (s + 1) := dvd_pow_self p (Nat.succ_ne_zero s)
  let f : (ZMod (p ^ (s + 1)))ˣ →* (ZMod p)ˣ :=
    ZMod.unitsMap hdiv
  have hsource : Nat.card (ZMod (p ^ (s + 1)))ˣ =
      p ^ s * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow_succ hp]
  have htarget : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hp]
  have hsurj : Function.Surjective f := ZMod.unitsMap_surjective hdiv
  have hindex : f.ker.index = p - 1 := by
    rw [Subgroup.index_ker]
    have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
    rw [hrange]
    simpa using htarget
  have hmul := f.ker.card_mul_index
  rw [hindex, hsource] at hmul
  have hcard : Nat.card f.ker = p ^ s :=
    Nat.eq_of_mul_eq_mul_right (Nat.sub_pos_of_lt hp.one_lt) hmul
  exact IsPGroup.of_card hcard

set_option synthInstance.maxHeartbeats 500000 in
-- The two-primary cyclotomic reduction builds a large tower of local-field instances.
set_option maxHeartbeats 3000000 in
/-- The two-primary prime-power conclusion, using exactly the cyclic
cyclotomic hypothesis in the statement. -/
private theorem twoPrimary
    (h46 : NontrivialNonsplitPrimes.{u})
    (n : ℕ) (K : Type u) [Field K] [NumberField K]
    (a : Kˣ) (hcyclic : CyclicPrimaryExtension K n)
    (hlocal : AENth K
      (2 ^ n.factorization 2) a) :
    a ∈ (powMonoidHom (2 ^ n.factorization 2) : Kˣ →* Kˣ).range := by
  obtain ⟨C, fieldC, numberFieldC, algebraKC, finiteKC, galoisKC,
    cyclotomicKC, cyclicKC⟩ := hcyclic
  letI : Field C := fieldC
  letI : NumberField C := numberFieldC
  letI : Algebra K C := algebraKC
  letI : FiniteDimensional K C := finiteKC
  letI : IsGalois K C := galoisKC
  letI : IsCyclotomicExtension {2 ^ n.factorization 2} K C := cyclotomicKC
  letI : IsCyclic Gal(C/K) := cyclicKC
  let r := n.factorization 2
  let q := 2 ^ r
  have hq : 0 < q := pow_pos (by omega) r
  letI : NeZero q := ⟨hq.ne'⟩
  let zeta := IsCyclotomicExtension.zeta q K C
  have hzeta : IsPrimitiveRoot zeta q :=
    IsCyclotomicExtension.zeta_spec q K C
  have hpGroup : IsPGroup 2 Gal(C/K) :=
    (zmod_units_p r).of_injective
      (hzeta.autToPow K) (hzeta.autToPow_injective K)
  have hroots : (primitiveRoots q C).Nonempty :=
    ⟨zeta, (mem_primitiveRoots hq).2 hzeta⟩
  let aC : Cˣ := Units.map (algebraMap K C) a
  have hlocalC : AENth C q aC :=
    hlocal.map
  have hpowerC : aC ∈ (powMonoidHom q : Cˣ →* Cˣ).range :=
    radicalExtensionStatement h46 q C hroots
      aC hlocalC
  exact cyclic_p_cyclotomic
    h46 2 r Nat.prime_two K C hpGroup a hlocal hpowerC

set_option synthInstance.maxHeartbeats 500000 in
-- The odd-primary fixed-field construction requires deeper Galois instance search.
set_option maxHeartbeats 5000000 in
/-- Step 3 for an odd prime: use the fixed field of the congruence subgroup
of the cyclotomic character, apply Step 2 above it, and descend by norm. -/
private theorem oddPrimePrimary
    (h46 : NontrivialNonsplitPrimes.{u})
    (p r : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hr : 0 < r)
    (K : Type u) [Field K] [NumberField K]
    (a : Kˣ) (hlocal : AENth K (p ^ r) a) :
    a ∈ (powMonoidHom (p ^ r) : Kˣ →* Kˣ).range := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  let q := p ^ r
  letI : NeZero q := ⟨pow_ne_zero r hp.ne_zero⟩
  let L := CyclotomicField q K
  letI : Field L := inferInstance
  letI : IsCyclotomicExtension {q} K L :=
    CyclotomicField.isCyclotomicExtension q K
  letI : FiniteDimensional K L :=
    IsCyclotomicExtension.finite_of_singleton q K L
  letI : IsGalois K L :=
    IsCyclotomicExtension.isGalois (S := {q}) (K := K) (L := L)
  have hcyclicL : IsCyclic Gal(L/K) :=
    by
      simpa [q] using
        (exercise_six_aut
          (p := p) (r := r) hp hp2 K L)
  letI : IsCyclic Gal(L/K) := hcyclicL
  let zeta := IsCyclotomicExtension.zeta q K L
  have hzeta : IsPrimitiveRoot zeta q :=
    IsCyclotomicExtension.zeta_spec q K L
  let hdiv : p ∣ q := by
    exact dvd_pow_self p hr.ne'
  let reduction : (ZMod q)ˣ →* (ZMod p)ˣ := ZMod.unitsMap hdiv
  let character : Gal(L/K) →* (ZMod p)ˣ :=
    reduction.comp (hzeta.autToPow K)
  let H : Subgroup Gal(L/K) := character.ker
  let C := IntermediateField.fixedField H
  letI : Algebra C L := C.val.toRingHom.toAlgebra
  letI : IsScalarTower K C L := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro x
    rfl
  have hHnormal : H.Normal := inferInstance
  letI : H.Normal := hHnormal
  have hCgalois : IsGalois K C := by
    dsimp [C]
    exact IsGalois.of_fixedField_normal_subgroup H
  letI : IsGalois K C := hCgalois
  letI : FiniteDimensional ℚ C := FiniteDimensional.trans ℚ K C
  letI : NumberField C := {}
  letI : IsGalois C L := IsGalois.tower_top_of_isGalois K C L
  have hcycloCL : IsCyclotomicExtension {q} C L := by
    apply (IsCyclotomicExtension.iff_singleton q C L).2
    refine ⟨⟨zeta, hzeta⟩, ?_⟩
    intro x
    have hx : x ∈ Algebra.adjoin K {b : L | b ^ q = 1} :=
      (IsCyclotomicExtension.iff_singleton q K L).1
        (inferInstance : IsCyclotomicExtension {q} K L) |>.2 x
    refine Algebra.adjoin_induction
      (p := fun y _ ↦ y ∈ Algebra.adjoin C {b : L | b ^ q = 1})
      (hx := hx) ?_ ?_ ?_ ?_
    · intro y hy
      exact Algebra.subset_adjoin hy
    · intro y
      have hy := (Algebra.adjoin C {b : L | b ^ q = 1}).algebraMap_mem
        (algebraMap K C y)
      rw [IsScalarTower.algebraMap_apply K C L]
      exact hy
    · intro x y _ _ hx hy
      exact (Algebra.adjoin C {b : L | b ^ q = 1}).add_mem hx hy
    · intro x y _ _ hx hy
      exact (Algebra.adjoin C {b : L | b ^ q = 1}).mul_mem hx hy
  letI : IsCyclotomicExtension {q} C L := hcycloCL
  have hkerP : IsPGroup p reduction.ker := by
    exact zmod_units_group p r hp hr
  have hHP : IsPGroup p H := by
    have hH : H = reduction.ker.comap (hzeta.autToPow K) := by
      ext sigma
      simp [H, character, reduction]
    rw [hH]
    exact hkerP.comap_of_injective
      (hzeta.autToPow K) (hzeta.autToPow_injective K)
  have hGalCLP : IsPGroup p Gal(L/C) :=
    IsPGroup.of_equiv hHP (IntermediateField.subgroupEquivAlgEquiv H)
  have hcyclicH : IsCyclic H := inferInstance
  have hcyclicCL : IsCyclic Gal(L/C) :=
    (IntermediateField.subgroupEquivAlgEquiv H).isCyclic.mp hcyclicH
  letI : IsCyclic Gal(L/C) := hcyclicCL
  have hdegreeDvd : Module.finrank K C ∣ p - 1 := by
    have hrange : Nat.card character.range ∣ Nat.card (ZMod p)ˣ :=
      character.range.card_subgroup_dvd_card
    have hcardRange : Nat.card character.range = Module.finrank K C := by
      calc
        Nat.card character.range = Nat.card (Gal(L/K) ⧸ H) :=
          Nat.card_congr (QuotientGroup.quotientKerEquivRange character).symm.toEquiv
        _ = Nat.card Gal(C/K) :=
          Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv
        _ = Module.finrank K C := IsGalois.card_aut_eq_finrank K C
    rw [hcardRange] at hrange
    have htarget : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
        Nat.totient_prime hp]
    rw [htarget] at hrange
    exact hrange
  have hdegreeCoprime : (Module.finrank K C).Coprime p := by
    apply Nat.Coprime.of_dvd_left hdegreeDvd
    exact (Nat.coprime_self_sub_left hp.one_le).2 (by simp)
  let aC : Cˣ := Units.map (algebraMap K C) a
  have hlocalC : AENth C q aC := hlocal.map
  let aL : Lˣ := Units.map (algebraMap C L) aC
  have hlocalL : AENth L q aL := hlocalC.map
  have hrootsL : (primitiveRoots q L).Nonempty :=
    ⟨zeta, (mem_primitiveRoots (pow_pos hp.pos r)).2 hzeta⟩
  have hpowerL : aL ∈ (powMonoidHom q : Lˣ →* Lˣ).range :=
    radicalExtensionStatement h46 q L hrootsL
      aL hlocalL
  have hpowerC : aC ∈ (powMonoidHom q : Cˣ →* Cˣ).range :=
    cyclic_p_cyclotomic
      h46 p r hp C L hGalCLP aC hlocalC hpowerL
  exact after_coprime_finrank
    hdegreeCoprime a hpowerC

/-- Steps 2 and 3, now proved rather than packaged as a bridge. -/
theorem primeBelowPower
    (h46 : NontrivialNonsplitPrimes.{u})
    (n : ℕ) (K : Type u) [Field K] [NumberField K] (a : Kˣ)
    (hn : 0 < n) (hcyclic : CyclicPrimaryExtension K n)
    (hlocal : AENth K n a) :
    ∀ p : n.primeFactors,
      a ∈ (powMonoidHom (p.1 ^ n.factorization p.1) : Kˣ →* Kˣ).range := by
  intro p
  let r := n.factorization p.1
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hr : 0 < r := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp p.2)
  have hdiv : p.1 ^ r ∣ n :=
    (hp.pow_dvd_iff_le_factorization hn.ne').2 le_rfl
  have hlocalPrime : AENth K (p.1 ^ r) a :=
    hlocal.of_dvd hdiv
  by_cases hp2 : p.1 = 2
  · have hlocalTwo : AENth K
        (2 ^ n.factorization 2) a := by
      simpa [r, hp2] using hlocalPrime
    simpa [r, hp2] using twoPrimary
      h46 n K a hcyclic hlocalTwo
  · exact oddPrimePrimary
      h46 p.1 r hp hp2 hr K a hlocalPrime

/-- Iterating the two-factor coprime-power lemma over a finite pairwise
coprime family of exponents. -/
private theorem finset_pairwise_coprime
    {G ι : Type*} [CommGroup G]
    (s : Finset ι) (e : ι → ℕ) (a : G)
    (hpair : Set.Pairwise (↑s) (Function.onFun Nat.Coprime e))
    (hpower : ∀ i ∈ s, a ∈ (powMonoidHom (e i) : G →* G).range) :
    a ∈ (powMonoidHom (∏ i ∈ s, e i) : G →* G).range := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      exact ⟨a, by simp⟩
  | cons i s hi ih =>
      rw [Finset.prod_cons]
      rw [Finset.coe_cons, Set.pairwise_insert] at hpair
      apply power_mul_coprime
      · exact Nat.Coprime.prod_right fun j hj ↦
          (hpair.2 j (by simp [hj]) fun hij ↦ hi (hij ▸ hj)).1
      · exact hpower i (by simp)
      · exact ih hpair.1 fun j hj ↦ hpower j (Finset.mem_cons_of_mem hj)

/-- Step 1 of Theorem 1.4: the prime-power assertions assemble to the
assertion for `n`, by unique factorization and pairwise coprimality of the
distinct prime-power factors. -/
theorem coprime_assembly
    (n : ℕ) (K : Type u) [Field K] [NumberField K] (a : Kˣ)
    (hn : 0 < n)
    (hpower : ∀ p : n.primeFactors,
      a ∈ (powMonoidHom (p.1 ^ n.factorization p.1) : Kˣ →* Kˣ).range) :
    a ∈ (powMonoidHom n : Kˣ →* Kˣ).range := by
  classical
  rw [Nat.prod_pow_primeFactors_factorization hn.ne']
  apply finset_pairwise_coprime
  · intro p _ q _ hpq
    exact Nat.pairwise_coprime_pow_primeFactors_factorization hpq
  · intro p _
    exact hpower p

/-- Theorem 1.4 from Proposition VII.4.6.  Theorem 1.1, cyclic
prime-power descent, odd-prime norm descent, and coprime assembly are all
discharged above. -/
theorem primeBelowStatement
    (h46 : NontrivialNonsplitPrimes.{u}) :
    ∀ (n : ℕ) (K : Type u) [Field K] [NumberField K],
    0 < n → CyclicPrimaryExtension K n →
    ∀ a : Kˣ, AENth K n a →
      a ∈ (powMonoidHom n : Kˣ →* Kˣ).range
  := by
  intro n K _ _ hn hcyclic a hlocal
  exact coprime_assembly n K a hn
    (primeBelowPower
      h46 n K a hn hcyclic hlocal)

end

end Towers.CField.LGPowers

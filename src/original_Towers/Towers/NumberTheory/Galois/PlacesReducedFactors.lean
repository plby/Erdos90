import Towers.NumberTheory.Ramification.KummerFactorization
import Towers.NumberTheory.Locals.HenselFactorization
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Milne, Chapter 8, Remark 8.3: finite places and reduced factors

For a monogenic extension of rings of integers, finite places above a fixed
finite place correspond to the prime ideals above its maximal ideal, and
Kummer--Dedekind identifies those primes with the irreducible factors of the
reduced minimal polynomial.

The additional Hensel assertion in Remark 8.3 says that the reduction of each
irreducible completed factor is a power of one irreducible polynomial.  It is
proved below from the general coprime-factor form of Hensel's lemma developed
in Chapter 7.
-/

namespace Towers.NumberTheory.Milne

open Algebra Ideal Polynomial UniqueFactorizationMonoid
open IsDedekindDomain IsLocalRing NumberField

attribute [local instance] Ideal.Quotient.field

noncomputable section

variable {K L : Type*} [Field K] [Field L]
  [NumberField K] [NumberField L] [Algebra K L]

local instance (p : HeightOneSpectrum (𝓞 K)) : p.asIdeal.IsMaximal := p.isMaximal

/-- The linear-factor consequence of Remark 8.3 available from the current
Hensel API: an irreducible generic-fiber polynomial cannot have a simple
residue root with a positive-degree complementary factor. -/
theorem not_coprime_irreducible
    {A E : Type*} [CommRing A] [HenselianLocalRing A]
    [Field E] [Algebra A E]
    (f : A[X]) (hf : f.Monic)
    (hfirr : Irreducible (f.map (algebraMap A E)))
    (a0 : ResidueField A) (h0 : (ResidueField A)[X])
    (hfactor : f.map (residue A) = (X - C a0) * h0)
    (hcoprime : IsCoprime (X - C a0) h0)
    (hh0 : 0 < h0.natDegree) : False := by
  obtain ⟨g, h, hg, hh, hfh, hgmap, hhmap, _⟩ :=
    hensel_lift_factorization f hf a0 h0 hfactor hcoprime
  have hmap : f.map (algebraMap A E) =
      g.map (algebraMap A E) * h.map (algebraMap A E) := by
    rw [hfh]
    exact Polynomial.map_mul _
  rcases hfirr.isUnit_or_isUnit hmap with hunitg | hunith
  · have hdeg : (g.map (algebraMap A E)).natDegree = 1 := by
      rw [hg.natDegree_map]
      rw [← hg.natDegree_map (residue A), hgmap]
      simp
    have hzero := Polynomial.natDegree_eq_zero_of_isUnit hunitg
    omega
  · have hdeg : (h.map (algebraMap A E)).natDegree = h0.natDegree := by
      rw [hh.natDegree_map, ← hh.natDegree_map (residue A), hhmap]
    have hzero := Polynomial.natDegree_eq_zero_of_isUnit hunith
    omega

/-- The Hensel assertion in Milne, Remark 8.3.  If a monic polynomial is
irreducible after passing from an adically complete local ring to a field,
then its reduction is a positive power of one monic irreducible residue
polynomial. -/
theorem residue_pow_irreducible
    {A E : Type*} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A]
    [Field E] [Algebra A E]
    (f : A[X]) (hf : f.Monic)
    (hfirr : Irreducible (f.map (algebraMap A E))) :
    ∃ g : (ResidueField A)[X],
      Irreducible g ∧ g.Monic ∧
        ∃ e : ℕ, 0 < e ∧ f.map (residue A) = g ^ e := by
  classical
  let f₀ : (ResidueField A)[X] := f.map (residue A)
  let s : Multiset (ResidueField A)[X] := normalizedFactors f₀
  have hf₀monic : f₀.Monic := hf.map (residue A)
  have hf₀ne : f₀ ≠ 0 := hf₀monic.ne_zero
  have hfpos : 0 < f.natDegree := by
    rw [← hf.natDegree_map (algebraMap A E)]
    exact hfirr.natDegree_pos
  have hf₀pos : 0 < f₀.natDegree := by
    change 0 < (f.map (residue A)).natDegree
    rwa [hf.natDegree_map]
  have hf₀nonunit : ¬ IsUnit f₀ := by
    intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  have hsne : s ≠ 0 := by
    intro hs
    apply hf₀nonunit
    exact (normalizedFactors_eq_zero_iff hf₀ne).mp hs
  obtain ⟨q, hqs⟩ := Multiset.exists_mem_of_ne_zero hsne
  have hqirr : Irreducible q :=
    irreducible_of_normalized_factor q hqs
  have hqmonic : q.Monic :=
    (Polynomial.mem_normalizedFactors_iff hf₀ne).mp hqs |>.2.1
  have hall : ∀ r ∈ s, r = q := by
    intro r hrs
    by_contra hrq
    let t : Multiset (ResidueField A)[X] :=
      s.filter fun a ↦ a ≠ q
    have hrt : r ∈ t := by
      exact Multiset.mem_filter.mpr ⟨hrs, hrq⟩
    have hcount : 0 < s.count q := Multiset.count_pos.mpr hqs
    have htmonic : t.prod.Monic := by
      simpa only [Multiset.map_id'] using
        monic_multiset_prod_of_monic t (fun a ↦ a) (by
          intro a ha
          have has : a ∈ s := (Multiset.mem_filter.mp ha).1
          exact (Polynomial.mem_normalizedFactors_iff hf₀ne).mp has |>.2.1)
    have hqcoprime : IsCoprime q t.prod := by
      have hpair : ∀ a ∈ t, IsCoprime q a := by
        intro a ha
        have has : a ∈ s := (Multiset.mem_filter.mp ha).1
        have hane : a ≠ q := (Multiset.mem_filter.mp ha).2
        have hairr : Irreducible a :=
          irreducible_of_normalized_factor a has
        have hamonic : a.Monic :=
          (Polynomial.mem_normalizedFactors_iff hf₀ne).mp has |>.2.1
        rcases hqirr.isCoprime_or_dvd a with hc | hdvd
        · exact hc
        · exact (hane <| (eq_of_monic_of_associated hqmonic hamonic
            (hqirr.associated_of_dvd hairr hdvd)).symm).elim
      have hprodCoprime : ∀ u : Multiset (ResidueField A)[X],
          (∀ a ∈ u, IsCoprime q a) → IsCoprime q u.prod := by
        intro u hu
        induction u using Multiset.induction_on with
        | empty => exact isCoprime_one_right
        | cons a u ih =>
            rw [Multiset.prod_cons]
            exact (hu a (Multiset.mem_cons_self a u)).mul_right <|
              ih fun b hb ↦ hu b (Multiset.mem_cons_of_mem hb)
      exact hprodCoprime t hpair
    have hfactor₀ : f₀ = q ^ s.count q * t.prod := by
      have hsplit := Multiset.filter_add_not (p := fun a ↦ a = q) s
      have hprod : s.prod = f₀ := by
        rw [prod_normalizedFactors_eq hf₀ne,
          (Polynomial.normalize_eq_self_iff_monic hf₀ne).2 hf₀monic]
      calc
        f₀ = s.prod := hprod.symm
        _ = (s.filter fun a ↦ a = q).prod *
            (s.filter fun a ↦ a ≠ q).prod := by
              rw [← Multiset.prod_add, hsplit]
        _ = q ^ s.count q * t.prod := by
              rw [Multiset.filter_eq', Multiset.prod_replicate]
    obtain ⟨g, h, hg, hh, hfh, hgmap, hhmap, _⟩ :=
      adic_hensel_factorization f hf
        (q ^ s.count q) t.prod (hqmonic.pow _) htmonic hfactor₀
        hqcoprime.pow_left
    have hgpos : 0 < g.natDegree := by
      rw [← hg.natDegree_map (residue A), hgmap,
        Polynomial.natDegree_pow]
      exact Nat.mul_pos hcount hqirr.natDegree_pos
    have htpos : 0 < t.prod.natDegree := by
      have hrdiv : r ∣ t.prod := Multiset.dvd_prod hrt
      have hrirr : Irreducible r :=
        irreducible_of_normalized_factor r hrs
      exact hrirr.natDegree_pos.trans_le
        (Polynomial.natDegree_le_of_dvd hrdiv htmonic.ne_zero)
    have hhpos : 0 < h.natDegree := by
      rw [← hh.natDegree_map (residue A), hhmap]
      exact htpos
    have hmap : f.map (algebraMap A E) =
        g.map (algebraMap A E) * h.map (algebraMap A E) := by
      rw [hfh, Polynomial.map_mul]
    rcases hfirr.isUnit_or_isUnit hmap with hgu | hhu
    · have hzero := Polynomial.natDegree_eq_zero_of_isUnit hgu
      rw [hg.natDegree_map] at hzero
      omega
    · have hzero := Polynomial.natDegree_eq_zero_of_isUnit hhu
      rw [hh.natDegree_map] at hzero
      omega
  have hsrep : s = Multiset.replicate s.card q :=
    Multiset.eq_replicate_card.mpr hall
  have hepos : 0 < s.card := Multiset.card_pos.mpr hsne
  refine ⟨q, hqirr, hqmonic, s.card, hepos, ?_⟩
  have hprod : s.prod = f₀ := by
    rw [prod_normalizedFactors_eq hf₀ne,
      (Polynomial.normalize_eq_self_iff_monic hf₀ne).2 hf₀monic]
  calc
    f.map (residue A) = f₀ := rfl
    _ = s.prod := hprod.symm
    _ = (Multiset.replicate s.card q).prod := congrArg Multiset.prod hsrep
    _ = q ^ s.card := Multiset.prod_replicate _ _

/-- Finite-place classes of `L` above `v` correspond to the prime ideals of
`𝓞 L` above the maximal ideal belonging to `v`. -/
def finitePlacesPrimes (v : FinitePlace K) :
    {w : FinitePlace L //
      w.maximalIdeal.asIdeal ∣
        Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.maximalIdeal.asIdeal} ≃
      v.maximalIdeal.asIdeal.primesOver (𝓞 L) :=
  ((FinitePlace.equivHeightOneSpectrum (K := L)).subtypeEquiv
      (fun _ => Iff.rfl)).trans
    (HeightOneSpectrum.equivPrimesOver (𝓞 L) v.maximalIdeal.ne_bot)

open Classical in
/-- Under the monogenicity hypothesis in Remark 8.3, primes above `p`
correspond to the normalized irreducible factors of the reduced minimal
polynomial. -/
def primesReducedMinpoly
    (p : HeightOneSpectrum (𝓞 K)) (α : 𝓞 L)
    (hα : Algebra.adjoin (𝓞 K) {α} = ⊤) :
    p.asIdeal.primesOver (𝓞 L) ≃
      {g : ((𝓞 K) ⧸ p.asIdeal)[X] //
        g ∈ normalizedFactors
          ((minpoly (𝓞 K) α).map (Ideal.Quotient.mk p.asIdeal))} := by
  let e₁ : p.asIdeal.primesOver (𝓞 L) ≃
      {P : Ideal (𝓞 L) //
        P ∈ normalizedFactors
          (p.asIdeal.map (algebraMap (𝓞 K) (𝓞 L)))} :=
    Equiv.setCongr (by
      ext P
      exact Ideal.mem_primesOver_iff_mem_normalizedFactors (𝓞 L) p.ne_bot)
  have hc :
      (conductor (𝓞 K) α).comap (algebraMap (𝓞 K) (𝓞 L)) ⊔ p.asIdeal = ⊤ := by
    rw [conductor_eq_top_iff_adjoin_eq_top.mpr hα, Ideal.comap_top, top_sup_eq]
  exact e₁.trans
    (KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
      p.isMaximal p.ne_bot hc (Algebra.IsIntegral.isIntegral α))

open Classical in
/-- Combining the finite-place and Kummer--Dedekind descriptions, normalized
finite-place classes above `v` are indexed by the irreducible factors of the
minimal polynomial modulo the prime belonging to `v`. -/
def reducedMinpolyFactors
    (v : FinitePlace K) (α : 𝓞 L)
    (hα : Algebra.adjoin (𝓞 K) {α} = ⊤) :
    {w : FinitePlace L //
      w.maximalIdeal.asIdeal ∣
        Ideal.map (algebraMap (𝓞 K) (𝓞 L)) v.maximalIdeal.asIdeal} ≃
      {g : ((𝓞 K) ⧸ v.maximalIdeal.asIdeal)[X] //
        g ∈ normalizedFactors
          ((minpoly (𝓞 K) α).map
            (Ideal.Quotient.mk v.maximalIdeal.asIdeal))} :=
  (finitePlacesPrimes v).trans
    (primesReducedMinpoly v.maximalIdeal α hα)

end

end Towers.NumberTheory.Milne

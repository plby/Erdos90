import Towers.NumberTheory.Discriminant.NumberFieldDiscriminant
import Towers.NumberTheory.Discriminant.FiniteIndexDiscriminant
import Towers.NumberTheory.Ramification.KummerFactorization
import Towers.NumberTheory.Ramification.RamificationDiscriminant
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Milne, Algebraic Number Theory, Theorem 4.9 and Corollary 4.10

A number field of degree greater than one has a ramified finite prime.  We express finite
ramification using `Algebra.IsUnramifiedAt` for the extension of rings of integers
`ℤ → 𝓞 K`.
-/

namespace Towers.NumberTheory.Milne

open nonZeroDivisors
open NumberField

/-- Theorem 4.9, discriminant form: a nontrivial number field has absolute discriminant
strictly greater than one. -/
theorem nontrivial_abs_discr
    (K : Type*) [Field K] [NumberField K]
    (hK : 1 < Module.finrank ℚ K) :
    1 < |NumberField.discr K| := by
  exact lt_trans (by norm_num) (nontrivial_discr_two K hK)

/-- The different of a nontrivial number field over `ℚ` is a proper ideal. -/
theorem nontrivial_different_top
    (K : Type*) [Field K] [NumberField K]
    (hK : 1 < Module.finrank ℚ K) :
    differentIdeal ℤ (𝓞 K) ≠ ⊤ := by
  intro htop
  have hnorm := NumberField.absNorm_differentIdeal K (𝓞 K)
  rw [htop, Ideal.absNorm_top] at hnorm
  have hnat : (NumberField.discr K).natAbs = 1 := hnorm.symm
  have habs : |NumberField.discr K| = 1 := by
    rw [Int.abs_eq_natAbs, hnat]
    simp
  linarith [nontrivial_abs_discr K hK]

/-- Theorem 4.9, ramification form: every nontrivial number field has a finite prime at which
`𝓞 K / ℤ` is not unramified. -/
theorem unramified_nontrivial_number
    (K : Type*) [Field K] [NumberField K]
    (hK : 1 < Module.finrank ℚ K) :
    ∃ (P : Ideal (𝓞 K)) (_ : P.IsPrime), P ≠ ⊥ ∧ ¬ Algebra.IsUnramifiedAt ℤ P := by
  obtain ⟨P, hPmax, hDP⟩ :=
    Ideal.exists_le_maximal (differentIdeal ℤ (𝓞 K))
      (nontrivial_different_top K hK)
  have hPprime : P.IsPrime := hPmax.isPrime
  letI : P.IsPrime := hPprime
  refine ⟨P, hPprime, ?_, ?_⟩
  · exact Ring.ne_bot_of_isMaximal_of_not_isField hPmax (RingOfIntegers.not_isField K)
  · rw [← dvd_different_ramified ℤ (𝓞 K) P]
    exact Ideal.dvd_iff_le.mpr hDP

/-- Theorem 4.9 in global form: a number field unramified at every nonzero finite prime over
`ℚ` has degree one. -/
theorem finrank_all_primes
    (K : Type*) [Field K] [NumberField K]
    (hunramified : ∀ (P : Ideal (𝓞 K)) (_ : P.IsPrime),
      P ≠ ⊥ → Algebra.IsUnramifiedAt ℤ P) :
    Module.finrank ℚ K = 1 := by
  by_contra hne
  have hK : 1 < Module.finrank ℚ K := by
    exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr
      ⟨Module.finrank_pos.ne', hne⟩
  obtain ⟨P, hPprime, hP0, hram⟩ :=
    unramified_nontrivial_number K hK
  exact hram (hunramified P hPprime hP0)

/-- Corollary 4.10 in integral-basis form: an integral basis of a nontrivial number field cannot
have discriminant `1` or `-1`.  In particular this applies to an integral power basis. -/
theorem discr_ne_neg
    (K : Type*) [Field K] [NumberField K]
    (hK : 1 < Module.finrank ℚ K)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℚ K) (hb : ∀ i, IsIntegral ℤ (b i)) :
    Algebra.discr ℚ b ≠ 1 ∧ Algebra.discr ℚ b ≠ -1 := by
  obtain ⟨d, hd⟩ :=
    sq_discr_basis K b hb
  have hnotunit : ¬ IsUnit (NumberField.discr K) := by
    rw [Int.isUnit_iff_abs_eq]
    exact ne_of_gt (nontrivial_abs_discr K hK)
  constructor
  · intro hone
    have hprodQ : (d : ℚ) ^ 2 * (NumberField.discr K : ℚ) = 1 := hd.symm.trans hone
    have hprodZ : d ^ 2 * NumberField.discr K = 1 := by
      exact_mod_cast hprodQ
    apply hnotunit
    rw [isUnit_iff_dvd_one]
    exact ⟨d ^ 2, by simpa [mul_comm] using hprodZ.symm⟩
  · intro hneg
    have hprodQ : (d : ℚ) ^ 2 * (NumberField.discr K : ℚ) = -1 := hd.symm.trans hneg
    have hprodZ : d ^ 2 * NumberField.discr K = -1 := by
      exact_mod_cast hprodQ
    apply hnotunit
    rw [isUnit_iff_dvd_one]
    have hdvdneg : NumberField.discr K ∣ (-1 : ℤ) :=
      ⟨d ^ 2, by simpa [mul_comm] using hprodZ.symm⟩
    exact dvd_trans hdvdneg (by norm_num)

/-- Corollary 4.10 for a power generator: the discriminant of the powers of an integral
primitive element in a nontrivial number field is never `1` or `-1`. -/
theorem integral_discr_neg
    (K : Type*) [Field K] [NumberField K]
    (hK : 1 < Module.finrank ℚ K) (pb : PowerBasis ℚ K)
    (hgen : IsIntegral ℤ pb.gen) :
    Algebra.discr ℚ pb.basis ≠ 1 ∧ Algebra.discr ℚ pb.basis ≠ -1 := by
  apply discr_ne_neg K hK pb.basis
  intro i
  simpa only [PowerBasis.coe_basis] using hgen.pow i

/-- The final divisibility step in Corollary 4.10.  Once the discriminant of a monic irreducible
integer polynomial is identified with the discriminant of its integral power basis, the standard
index-squared formula supplies the divisibility hypothesis below. -/
theorem integer_discr_dvd
    (K : Type*) [Field K] [NumberField K]
    (hK : 1 < Module.finrank ℚ K) (f : Polynomial ℤ)
    (hdiv : NumberField.discr K ∣ f.discr) :
    f.discr ≠ 1 ∧ f.discr ≠ -1 := by
  have hnotunit : ¬ IsUnit (NumberField.discr K) := by
    rw [Int.isUnit_iff_abs_eq]
    exact ne_of_gt (nontrivial_abs_discr K hK)
  constructor <;> intro hf
  · apply hnotunit
    rw [isUnit_iff_dvd_one]
    simpa [hf] using hdiv
  · apply hnotunit
    rw [isUnit_iff_dvd_one]
    exact dvd_trans (by simpa [hf] using hdiv) (by norm_num)

/-- Corollary 4.10: an irreducible monic integer polynomial of degree greater than one
cannot have discriminant `1` or `-1`. -/
theorem integer_discr_neg
    (f : Polynomial ℤ) (hfmonic : f.Monic) (hfirr : Irreducible f)
    (hdeg : 1 < f.natDegree) :
    f.discr ≠ 1 ∧ f.discr ≠ -1 := by
  let g : Polynomial ℚ := f.map (Int.castRingHom ℚ)
  have hgmonic : g.Monic := hfmonic.map (Int.castRingHom ℚ)
  have hgirr : Irreducible g := by
    exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      hfmonic.isPrimitive).mp hfirr
  letI : Fact (Irreducible g) := ⟨hgirr⟩
  let pb : PowerBasis ℚ (AdjoinRoot g) := AdjoinRoot.powerBasis hgirr.ne_zero
  have hK : 1 < Module.finrank ℚ (AdjoinRoot g) := by
    rw [pb.finrank]
    change 1 < g.natDegree
    simpa [g, hfmonic.natDegree_map] using hdeg
  have hgenIntegral : IsIntegral ℤ pb.gen := by
    dsimp [pb]
    refine ⟨f, hfmonic, ?_⟩
    change Polynomial.aeval (AdjoinRoot.root g) f = 0
    rw [← Polynomial.aeval_map_algebraMap ℚ]
    change Polynomial.aeval (AdjoinRoot.root g) g = 0
    calc
      Polynomial.aeval (AdjoinRoot.root g) g =
          AdjoinRoot.mk g (g.map (algebraMap ℚ ℚ)) :=
        AdjoinRoot.aeval_eq_of_algebra g g
      _ = 0 := by simp
  have hpb := integral_discr_neg
    (AdjoinRoot g) hK pb hgenIntegral
  have hpdisc : Algebra.discr ℚ pb.basis = g.discr := by
    rw [basis_discr_minpoly pb]
    dsimp [pb]
    have hmin : minpoly ℚ (AdjoinRoot.root g) = g := by
      simpa [hgmonic.leadingCoeff] using
        (AdjoinRoot.minpoly_root (K := ℚ) hgirr.ne_zero)
    rw [hmin]
  have hmapdisc : (f.discr : ℚ) = g.discr := by
    simpa [g] using polynomial_discr_monic
      (Int.castRingHom ℚ) f hfmonic (by omega : 0 < f.natDegree)
  constructor
  · intro hf
    apply hpb.1
    rw [hpdisc, ← hmapdisc, hf]
    norm_num
  · intro hf
    apply hpb.2
    rw [hpdisc, ← hmapdisc, hf]
    norm_num

end Towers.NumberTheory.Milne

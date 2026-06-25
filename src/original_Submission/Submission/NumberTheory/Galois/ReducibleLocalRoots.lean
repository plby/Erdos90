import Mathlib.NumberTheory.LegendreSymbol.Basic
import Submission.NumberTheory.Density.SplittingPrimeDensity

/-!
# Milne, Chapter 8, Remark 8.40(d)

The reducible polynomial `(X² - 2)(X² - 3)(X² - 6)` has a root modulo every
prime.  This is Milne's counterexample to the corresponding assertion for
reducible polynomials.
-/

namespace Submission.NumberTheory.Milne

open IsDedekindDomain Module NumberField Polynomial

noncomputable section

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

/-- A Galois extension in which all but finitely many primes split completely
has degree one. -/
theorem splitting_compl_chebotarev
    (hfinite : (splittingPrimes K L)ᶜ.Finite)
    (hcheb : ChebotarevDensityTheorem K L) :
    finrank K L = 1 := by
  have hcofinite : PNDensit K (splittingPrimes K L) 1 := by
    have h := (natural_density_univ K).diff_of_finite K hfinite
    simpa using h
  have hdensity := splitting_density_chebotarev K L hcheb
  have hrecip : (1 / finrank K L : ℝ) = 1 :=
    tendsto_nhds_unique hdensity hcofinite
  have hn : (finrank K L : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := K) (M := L)).ne'
  field_simp [hn] at hrecip
  exact_mod_cast hrecip.symm

/-- If a polynomial splits over such an extension, it already splits over the
base field. -/
theorem splits_cofinite_chebotarev
    (f : K[X]) (hsplits : (f.map (algebraMap K L)).Splits)
    (hfinite : (splittingPrimes K L)ᶜ.Finite)
    (hcheb : ChebotarevDensityTheorem K L) :
    f.Splits := by
  have hdegree : finrank K L = 1 :=
    splitting_compl_chebotarev
      hfinite hcheb
  have hsurjective : Function.Surjective (algebraMap K L) := by
    have hlinear : Function.Surjective (Algebra.linearMap K L) :=
      surjective_of_nonzero_of_finrank_eq_one (f := Algebra.linearMap K L)
        hdegree (by
          intro hzero
          have h := congrArg (fun g : K →ₗ[K] L => g 1) hzero
          exact (one_ne_zero : (1 : L) ≠ 0) (by simp at h))
    exact hlinear
  exact hsplits.of_splits_map (algebraMap K L)
    (fun x _ => hsurjective x)

/-- The reducible polynomial from Milne, Remark 8.40(d). -/
noncomputable def reducibleLocalRoots (R : Type*) [CommRing R] : R[X] :=
  (X ^ 2 - C 2) * (X ^ 2 - C 3) * (X ^ 2 - C 6)

/-- At every prime, at least one of `2`, `3`, and `6` is a square. -/
theorem square_or_six (p : ℕ) [Fact p.Prime] :
    ∃ x : ZMod p, x ^ 2 = 2 ∨ x ^ 2 = 3 ∨ x ^ 2 = 6 := by
  by_cases h2 : IsSquare (2 : ZMod p)
  · obtain ⟨x, hx⟩ := h2
    exact ⟨x, Or.inl (by simpa [pow_two] using hx.symm)⟩
  by_cases h3 : IsSquare (3 : ZMod p)
  · obtain ⟨x, hx⟩ := h3
    exact ⟨x, Or.inr (Or.inl (by simpa [pow_two] using hx.symm))⟩
  have hleg2 : legendreSym p 2 = -1 :=
    (@legendreSym.eq_neg_one_iff' p _ 2).2 h2
  have hleg3 : legendreSym p 3 = -1 :=
    (@legendreSym.eq_neg_one_iff' p _ 3).2 h3
  have hleg6 : legendreSym p 6 = 1 := by
    rw [show (6 : ℤ) = 2 * 3 by norm_num, legendreSym.mul, hleg2, hleg3]
    norm_num
  have h6ne : (6 : ZMod p) ≠ 0 := by
    intro h6
    have hmul : (2 : ZMod p) * 3 = 0 := by
      norm_num at h6 ⊢
      exact h6
    rcases mul_eq_zero.mp hmul with h2zero | h3zero
    · exact h2 ⟨0, by simp [h2zero]⟩
    · exact h3 ⟨0, by simp [h3zero]⟩
  have h6square : IsSquare (6 : ZMod p) :=
    (@legendreSym.eq_one_iff' p _ 6 h6ne).1 hleg6
  obtain ⟨x, hx⟩ := h6square
  exact ⟨x, Or.inr (Or.inr (by simpa [pow_two] using hx.symm))⟩

/-- Milne's reducible counterexample has a root modulo every prime. -/
theorem root_mod_prime (p : ℕ) [Fact p.Prime] :
    ∃ x : ZMod p, eval x (reducibleLocalRoots (ZMod p)) = 0 := by
  obtain ⟨x, hx | hx | hx⟩ :=
    square_or_six p
  · exact ⟨x, by simp [reducibleLocalRoots, hx]⟩
  · exact ⟨x, by simp [reducibleLocalRoots, hx]⟩
  · exact ⟨x, by simp [reducibleLocalRoots, hx]⟩

end

end Submission.NumberTheory.Milne

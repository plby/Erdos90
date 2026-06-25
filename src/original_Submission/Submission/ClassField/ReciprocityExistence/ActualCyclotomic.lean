import Submission.ClassField.ReciprocityExistence.ActualLocalProduct
import Submission.ClassField.ReciprocityExistence.CyclotomicReduction

/-!
# Example VII.8.2 for arbitrary conductor with literal local factors

Combining the prime-power restriction argument with the actual `Q_p^x`
local-factor package gives the source's full reduction for a rational
cyclotomic extension of arbitrary conductor.
-/

namespace Submission.CField.RExist

open Submission.CField.Ideles
open Submission.CField.Recip

noncomputable section

/-- **Example VII.8.2, arbitrary conductor, literal-local-map form.**
If each prime-power restriction has the three local products displayed in
the source, then the full cyclotomic Artin product is trivial on rational
principal idèles. -/
theorem cyclotomic_reciprocity_actual
    (m : ℕ) [NeZero m]
    (L : Type*) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L]
    (F : m.primeFactors → Type*)
    [∀ p, Field (F p)] [∀ p, NumberField (F p)]
    [∀ p, IsCyclotomicExtension
      {p.1 ^ m.factorization p.1} ℚ (F p)]
    [∀ p, Algebra (F p) L] [∀ p, IsGalois ℚ (F p)]
    (phi : IdeleGroup ℤ ℚ →* Gal(L/ℚ))
    (hdata : ∀ p : m.primeFactors,
      letI : Fact p.1.Prime :=
        ⟨Nat.prime_of_mem_primeFactors p.2⟩
      letI : NeZero (p.1 ^ m.factorization p.1) :=
        ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
      PAData
        p.1 (m.factorization p.1) (F p)
          ((AlgEquiv.restrictNormalHom (F p)).comp phi)) :
    ∀ x : ℚˣ, phi (principalIdele ℤ ℚ x) = 1 := by
  apply cyclotomic_principal_reciprocity m L F phi
  intro p
  letI : Fact p.1.Prime :=
    ⟨Nat.prime_of_mem_primeFactors p.2⟩
  letI : NeZero (p.1 ^ m.factorization p.1) :=
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
  exact (hdata p).prime_power_artindata
    p.1 (m.factorization p.1) (F p)
      ((AlgEquiv.restrictNormalHom (F p)).comp phi)

end

end Submission.CField.RExist

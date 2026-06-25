import Submission.ClassField.ReciprocityExistence.ActualCyclotomic

/-!
# Prime-power subfields of a rational cyclotomic field

For every prime-power factor `p ^ m.factorization p` of a nonzero conductor
`m`, the corresponding power of a primitive `m`th root is primitive of that
prime-power order.  Adjoining it gives the concrete family of subfields used
in the first reduction of Example VII.8.2.
-/

namespace Submission.CField.RExist

open NumberField
open Submission.CField.Ideles
open Submission.CField.Recip

noncomputable section

/-- The prime-power cyclotomic subfield of `Q(zeta_m)` belonging to a prime
factor `p` of `m`. -/
noncomputable def primePowerSubfield
    (m : ℕ) [NeZero m]
    (L : Type*) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L]
    (p : m.primeFactors) : IntermediateField ℚ L :=
  IntermediateField.adjoin ℚ
    {IsCyclotomicExtension.zeta m ℚ L ^
      (m / (p.1 ^ m.factorization p.1))}

/-- The displayed generator of `primePowerSubfield` is primitive
of order `p ^ m.factorization p`. -/
theorem subfield_zeta_primitive
    (m : ℕ) [NeZero m]
    (L : Type*) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L]
    (p : m.primeFactors) :
    IsPrimitiveRoot
      (IsCyclotomicExtension.zeta m ℚ L ^
        (m / (p.1 ^ m.factorization p.1)))
      (p.1 ^ m.factorization p.1) := by
  have hp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hdiv : p.1 ^ m.factorization p.1 ∣ m :=
    (hp.pow_dvd_iff_le_factorization (NeZero.ne m)).2 le_rfl
  exact (IsCyclotomicExtension.zeta_spec m ℚ L).pow
    (NeZero.pos m) (Nat.div_mul_cancel hdiv).symm

noncomputable instance subfield_cyclotomic_extension
    (m : ℕ) [NeZero m]
    (L : Type*) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L]
    (p : m.primeFactors) :
    IsCyclotomicExtension {p.1 ^ m.factorization p.1} ℚ
      (primePowerSubfield m L p) := by
  letI : NeZero (p.1 ^ m.factorization p.1) :=
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
  exact (subfield_zeta_primitive m L p)
    |>.intermediateField_adjoin_isCyclotomicExtension ℚ

noncomputable instance prime_subfield_galois
    (m : ℕ) [NeZero m]
    (L : Type*) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L]
    (p : m.primeFactors) :
    IsGalois ℚ (primePowerSubfield m L p) := by
  letI : NeZero (p.1 ^ m.factorization p.1) :=
    ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
  exact IsCyclotomicExtension.isGalois
    {p.1 ^ m.factorization p.1} ℚ (primePowerSubfield m L p)

/-- Example VII.8.2 for arbitrary conductor, with its prime-power subfields
chosen canonically inside the given rational cyclotomic field. -/
theorem reciprocity_subfield_data
    (m : ℕ) [NeZero m]
    (L : Type*) [Field L] [NumberField L]
    [IsCyclotomicExtension {m} ℚ L]
    (phi : IdeleGroup ℤ ℚ →* Gal(L/ℚ))
    (hdata : ∀ p : m.primeFactors,
      letI : Fact p.1.Prime :=
        ⟨Nat.prime_of_mem_primeFactors p.2⟩
      letI : NeZero (p.1 ^ m.factorization p.1) :=
        ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).ne_zero⟩
      PAData
        p.1 (m.factorization p.1) (primePowerSubfield m L p)
          ((AlgEquiv.restrictNormalHom
            (primePowerSubfield m L p)).comp phi)) :
    ∀ x : ℚˣ, phi (principalIdele ℤ ℚ x) = 1 :=
  cyclotomic_reciprocity_actual
    m L (fun p => ↥(primePowerSubfield m L p)) phi hdata

end

end Submission.CField.RExist

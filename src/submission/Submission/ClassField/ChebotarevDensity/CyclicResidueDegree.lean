import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Submission.ClassField.ChebotarevDensity.Density

/-!
# Appendix exercise A-10: residue degrees in cyclic extensions

For an unramified prime in a cyclic extension, the residue degree is the order
of its Frobenius element.  The arithmetic identification is part of the
Frobenius infrastructure documented in Chapter VIII, Section 7.  Here we prove
the remaining density calculation abstractly: if every Frobenius value has
density `1 / |G|`, then the primes whose Frobenius has order `d` have density
`phi(d) / |G|`.
-/

namespace Submission.CField.CDensit.CRDegree

open IsDedekindDomain NumberField
open Submission.NumberTheory.Milne

noncomputable section

variable (K : Type*) [Field K] [NumberField K]
variable {G : Type*} [Group G] [Fintype G]

/-- Primes whose Frobenius value belongs to a prescribed finite set. -/
def primesFrobeniusElements
    (frobenius : HeightOneSpectrum (𝓞 K) → Option G)
    (elements : Finset G) : Set (HeightOneSpectrum (𝓞 K)) :=
  {p | ∃ sigma ∈ elements, frobenius p = some sigma}

omit [NumberField K] [Fintype G] in
@[simp]
theorem primes_elements_empty
    (frobenius : HeightOneSpectrum (𝓞 K) → Option G) :
    primesFrobeniusElements K frobenius ∅ = ∅ := by
  ext p
  simp [primesFrobeniusElements]

/-- A finite disjoint union of singleton Frobenius fibers has density equal to
the number of allowed values divided by the order of the group. -/
theorem primes_elements_density
    (frobenius : HeightOneSpectrum (𝓞 K) → Option G)
    (hsingle : ∀ sigma : G,
      PNDensit K {p | frobenius p = some sigma}
        (1 / Fintype.card G))
    (elements : Finset G) :
    PNDensit K
      (primesFrobeniusElements K frobenius elements)
      ((elements.card : ℝ) / Fintype.card G) := by
  classical
  induction elements using Finset.induction_on with
  | empty =>
      simpa using
        (prime_natural_density K
          (Set.finite_empty : (∅ : Set (HeightOneSpectrum (𝓞 K))).Finite))
  | @insert sigma elements hsigma ih =>
      have hdisjoint :
          Disjoint {p | frobenius p = some sigma}
            (primesFrobeniusElements K frobenius elements) := by
        apply Set.disjoint_left.2
        intro p hp hpElements
        rcases hpElements with ⟨tau, htau, hpTau⟩
        have : sigma = tau := Option.some.inj (hp.symm.trans hpTau)
        exact hsigma (this ▸ htau)
      have hunion := (hsingle sigma).union_of_disjoint K ih hdisjoint
      have hsets :
          primesFrobeniusElements K frobenius (insert sigma elements) =
            {p | frobenius p = some sigma} ∪
              primesFrobeniusElements K frobenius elements := by
        ext p
        simp [primesFrobeniusElements]
      rw [hsets]
      simpa [Finset.card_insert_of_notMem hsigma, Nat.cast_add, add_div,
        one_div, add_comm] using hunion

/-- Exercise A-10, conditional density form.  In a finite cyclic group the
number of Frobenius elements of exact order `d` is Euler's totient `phi(d)`. -/
theorem cyclic_frobenius_density [IsCyclic G]
    (frobenius : HeightOneSpectrum (𝓞 K) → Option G)
    (hsingle : ∀ sigma : G,
      PNDensit K {p | frobenius p = some sigma}
        (1 / Fintype.card G))
    {d : ℕ} (hd : d ∣ Fintype.card G) :
    PNDensit K
      (primesFrobeniusElements K frobenius
        (Finset.univ.filter fun sigma => orderOf sigma = d))
      ((Nat.totient d : ℝ) / Fintype.card G) := by
  have h := primes_elements_density K frobenius hsingle
    (Finset.univ.filter fun sigma => orderOf sigma = d)
  rw [IsCyclic.card_orderOf_eq_totient hd] at h
  exact h

end

end Submission.CField.CDensit.CRDegree

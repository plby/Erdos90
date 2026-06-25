import Submission.ClassField.DirichletDensity.DegreeOneIdeals

/-!
# Chapter VI, Section 4, Corollary 4.6
-/

namespace Submission.CField.DDensit

open IsDedekindDomain NumberField Set
open Submission.CField.PDensit

noncomputable section

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- **Corollary VI.4.6 (source statement).**  Intersecting a set of primes
having Dirichlet density with the degree-one primes does not change its
density. -/
def ComplInterContains : Prop :=
  ∀ (S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) (δ : ℝ),
    PrimeDirichletDensity K S δ →
      PrimeDirichletDensity K (degreePrimeIdeals K ∩ S) δ

/-- Every subcollection of the complementary primes still satisfies
Proposition 3.2's "no prime absolute norm" hypothesis. -/
theorem compl_inter_contains
    (S : Set (HeightOneSpectrum (NumberField.RingOfIntegers K))) :
    ContainsNoAbsolute K ((degreePrimeIdeals K)ᶜ ∩ S) := by
  intro p hp hprime
  exact hp.1 hprime

/-- Proposition 3.2 and Proposition 4.1 give density zero to the portion of
`S` outside the degree-one primes.  Proposition 4.4(d), applied to the
resulting disjoint decomposition of `S`, gives the corollary. -/
theorem inter_41_44
    (h32 : (∀ T : Set (HeightOneSpectrum (NumberField.RingOfIntegers K)),
          ContainsNoAbsolute K T → PrimePolarDensity K T 0))
    (h41 : PolarDirichletBridge.{u})
    (h44d : RightSubtractionInput K) :
    ComplInterContains K := by
  intro S δ hS
  let T := degreePrimeIdeals K
  let B := Tᶜ ∩ S
  have hBpolar : PrimePolarDensity K B 0 := by
    exact h32 B
      (compl_inter_contains K S)
  have hBdirichlet : PrimeDirichletDensity K B 0 :=
    h41.1 K B 0 hBpolar
  have hdecomp : S = (T ∩ S) ∪ B := by
    ext p
    constructor
    · intro hpS
      by_cases hpT : p ∈ T
      · exact Or.inl ⟨hpT, hpS⟩
      · exact Or.inr ⟨hpT, hpS⟩
    · rintro (hp | hp)
      · exact hp.2
      · exact hp.2
  have hdis : Disjoint (T ∩ S) B := by
    exact Set.disjoint_left.2 fun p hpGood hpBad ↦ hpBad.1 hpGood.1
  have hsubtract := h44d S (T ∩ S) B δ 0 hdecomp hdis
    hS hBdirichlet
  simpa [T, B] using hsubtract

end

end Submission.CField.DDensit

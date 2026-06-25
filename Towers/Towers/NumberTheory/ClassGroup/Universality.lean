import Mathlib

/-!
# External class-group realization results cited before Milne, Example 3.22

Milne cites, without proof, two global realization theorems: Gauss's result that quadratic
class groups can have arbitrarily many cyclic factors of even order, and Claborn's theorem
that every abelian group occurs as the class group of a Dedekind domain.  We record precise
propositions for those source-delegated assertions, without adding axioms.
-/

namespace Towers.NumberTheory.Milne

open scoped NumberField

universe u

/-- The group-theoretic content of having at least `n` cyclic factors of even order: the
class group contains an elementary abelian `2`-subgroup of rank `n`. -/
def GaussEvenTheorem : Prop :=
  ∀ n : ℕ,
    ∃ (K : Type u) (fieldK : Field K),
      letI : Field K := fieldK
      ∃ numberFieldK : NumberField K,
        letI : NumberField K := numberFieldK
        Module.finrank ℚ K = 2 ∧
          ∃ f : (Fin n → ZMod 2) →* ClassGroup (𝓞 K),
            Function.Injective f

/-- **Claborn's theorem.** Every abelian group is isomorphic to the ideal class group of
some Dedekind domain.  Milne cites the 1966 paper and gives no proof. -/
def ClabornRealizationTheorem : Prop :=
  ∀ (G : Type u) [CommGroup G],
    ∃ (A : Type (u + 1)) (ringA : CommRing A),
      letI : CommRing A := ringA
      ∃ domainA : IsDomain A,
        letI : IsDomain A := domainA
        ∃ dedekindA : IsDedekindDomain A,
          letI : IsDedekindDomain A := dedekindA
          Nonempty (ClassGroup A ≃* G)

end Towers.NumberTheory.Milne

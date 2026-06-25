import Towers.ClassField.Shifting.SubsingletonLinearEquiv

/-!
# Milne, Class Field Theory, Proposition III.1.1: cohomological reduction

For a finite cyclic group, vanishing of `H¹` together with surjectivity of the
norm from coinvariants to invariants implies vanishing in every Tate degree.
These are exactly the two inputs in Milne's proof for the unit group of an
unramified local extension: Hilbert 90 supplies the first after splitting
`Lˣ ≃ U_L × ℤ`, and Proposition III.1.2 supplies the second.
-/

namespace Towers.CField.UCohom

open CategoryTheory Representation
open Shifting

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

/-- **Proposition III.1.1, cohomological core.** For a finite cyclic group,
`H¹(G,A) = 0` and surjectivity of the norm imply Tate acyclicity.

The conclusion lists the four ranges currently used to represent
integer-indexed Tate cohomology in the project: positive cohomology, degrees
zero and minus one, and positive homology. -/
theorem tate_acyclic_surjective
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (h₁ : Subsingleton (groupCohomology A 1))
    (hnorm : Function.Surjective (normCoinvariantsInvariants A)) :
    (∀ n : ℕ, 0 < n → Subsingleton (groupCohomology A n)) ∧
      Subsingleton (tateCohomologyZero A) ∧
      Subsingleton (tateCohomologyOne A) ∧
      ∀ n : ℕ, 0 < n → Subsingleton (groupHomology A n) := by
  have h₀ : Subsingleton (tateCohomologyZero A) := by
    rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
    exact hnorm
  have h₂ : Subsingleton (groupCohomology A 2) := by
    letI := h₀
    exact (tateCohomologyTwo A g hg).symm.injective.subsingleton
  exact tate_subsingleton_cyclic A g hg h₁ h₂

end

end Towers.CField.UCohom

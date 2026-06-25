import Towers.ClassField.Shifting.GroupPeriodicityOdd

/-!
# Milne, Class Field Theory, Theorem II.3.10: cyclic case

This is the first case in Milne's proof of Theorem II.3.10.  For a finite
cyclic group, the explicit cyclic resolutions identify every Tate degree
with either `H¹` or `H²`.
-/

namespace Towers.CField.Shifting

open CategoryTheory Representation

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

private theorem subsingleton_linear_equiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] [Module k A] [Module k B]
    (e : A ≃ₗ[k] B) (hB : Subsingleton B) : Subsingleton A := by
  letI : Subsingleton B := hB
  exact e.injective.subsingleton

set_option linter.unusedFintypeInType false in
/-- For a cyclic group, vanishing of `H¹` and `H²` implies vanishing in
every positive cohomological degree. -/
theorem subsingleton_cohomology_cyclic
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (h₁ : Subsingleton (groupCohomology A 1))
    (h₂ : Subsingleton (groupCohomology A 2))
    (n : ℕ) (hn : 0 < n) : Subsingleton (groupCohomology A n) := by
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · letI : NeZero n := NeZero.of_pos hn
    exact subsingleton_linear_equiv
      ((Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg n hnEven).toLinearEquiv.trans
        (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 even_two).symm.toLinearEquiv)
      h₂
  · exact subsingleton_linear_equiv
      ((Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg n hnOdd).toLinearEquiv.trans
        (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 odd_one).symm.toLinearEquiv)
      h₁

set_option linter.unusedFintypeInType false in
/-- For a cyclic group, vanishing of `H¹` and `H²` implies vanishing in
every positive homological degree, hence in every Tate degree below `-1`. -/
theorem subsingleton_homology_cyclic
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (h₁ : Subsingleton (groupCohomology A 1))
    (h₂ : Subsingleton (groupCohomology A 2))
    (n : ℕ) (hn : 0 < n) : Subsingleton (groupHomology A n) := by
  letI := Classical.decEq G
  rcases Nat.even_or_odd n with hnEven | hnOdd
  · letI : NeZero n := NeZero.of_pos hn
    exact subsingleton_linear_equiv
      ((Rep.FiniteCyclicGroup.groupHomologyIsoEven A g hg n hnEven).toLinearEquiv.trans
        (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 odd_one).symm.toLinearEquiv)
      h₁
  · exact subsingleton_linear_equiv
      ((Rep.FiniteCyclicGroup.groupHomologyIsoOdd A g hg n hnOdd).toLinearEquiv.trans
        (Rep.FiniteCyclicGroup.groupCohomologyIsoEven A g hg 2 even_two).symm.toLinearEquiv)
      h₂

set_option linter.unusedFintypeInType false in
/-- **Theorem II.3.10, cyclic case.** If `H¹(G,A)` and `H²(G,A)` vanish
for a finite cyclic group, then all of its Tate cohomology groups vanish.

Because the project represents Tate degrees by three existing theories, the
conclusion lists positive cohomology, degrees `0` and `-1`, and positive
homology (the degrees below `-1`) separately. -/
theorem tate_subsingleton_cyclic
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (h₁ : Subsingleton (groupCohomology A 1))
    (h₂ : Subsingleton (groupCohomology A 2)) :
    (∀ n : ℕ, 0 < n → Subsingleton (groupCohomology A n)) ∧
      Subsingleton (tateCohomologyZero A) ∧
      Subsingleton (tateCohomologyOne A) ∧
      ∀ n : ℕ, 0 < n → Subsingleton (groupHomology A n) := by
  refine ⟨subsingleton_cohomology_cyclic A g hg h₁ h₂, ?_, ?_,
    subsingleton_homology_cyclic A g hg h₁ h₂⟩
  · exact subsingleton_linear_equiv
      (tateCohomologyTwo A g hg) h₂
  · exact subsingleton_linear_equiv
      (tateCohomologyNeg A g hg) h₁

end

end Towers.CField.Shifting

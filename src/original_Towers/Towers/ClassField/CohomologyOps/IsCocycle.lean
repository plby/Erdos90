import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-!
# Class Field Theory, Chapter II, Example 1.20

This file proves Milne's elementary iteration formula for a crossed
homomorphism.  Mathlib calls the crossed-homomorphism condition
`groupCohomology.IsCocycle₁`.
-/

namespace Towers.CField.COps

open CategoryTheory
open groupCohomology
open scoped BigOperators

universe u

/-- Example 1.20: a crossed homomorphism evaluated at `g^n` is the sum of the
translates of its value at `g`. -/
theorem IsCocycle₁.map_pow
    {G A : Type*} [Monoid G] [AddCommGroup A] [MulAction G A]
    {f : G → A} (hf : IsCocycle₁ f) (g : G) (n : ℕ) :
    f (g ^ n) = ∑ i ∈ Finset.range n, g ^ i • f g := by
  induction n with
  | zero =>
      simp [map_one_of_isCocycle₁ hf]
  | succ n ih =>
      rw [pow_succ, hf, ih]
      simp [Finset.sum_range_succ, add_comm]

/-- If `g^n = 1`, the orbit sum of the value of a crossed homomorphism at
`g` vanishes.  For a generator of a finite cyclic group this is equation
(17) in Example 1.20. -/
theorem IsCocycle₁.sum_smul_eq_zero_of_pow_eq_one
    {G A : Type*} [Monoid G] [AddCommGroup A] [MulAction G A]
    {f : G → A} (hf : IsCocycle₁ f) {g : G} {n : ℕ} (hg : g ^ n = 1) :
    ∑ i ∈ Finset.range n, g ^ i • f g = 0 := by
  rw [← IsCocycle₁.map_pow hf g n, hg, map_one_of_isCocycle₁ hf]

/-- **Example II.1.20, cyclic cohomology formula.** Choosing a generator
identifies `H¹(G,A)` with the homology of
`A --(σ - 1)--> A --Nm_G--> A`, namely
`ker(Nm_G) / range(σ - 1)`. -/
noncomputable def cyclic1Iso
    {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]
    (A : Rep k G) (sigma : G)
    (hgen : ∀ g, g ∈ Subgroup.zpowers sigma) :
    H1 A ≅
      (Rep.FiniteCyclicGroup.subCompNormHom A sigma).homology :=
  Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A sigma hgen 1 (by simp)

/-- In the cyclic description of `H¹`, a norm-zero element represents the
zero class exactly when it lies in the image of `σ - 1`; this is Milne's
criterion for the crossed homomorphism to be principal. -/
theorem cyclic_h_1
    {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]
    (A : Rep k G) (sigma : G)
    (hgen : ∀ g, g ∈ Subgroup.zpowers sigma)
    (x : LinearMap.ker A.norm.hom.toLinearMap) :
    Rep.FiniteCyclicGroup.groupCohomologyπOdd A sigma hgen 1 (by simp) x = 0 ↔
      x.1 ∈ LinearMap.range
        (A.applyAsHom sigma - 𝟙 A).hom.toLinearMap :=
  Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff
    A sigma hgen 1 (by simp) x

end Towers.CField.COps

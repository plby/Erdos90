import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.Archimedean
import Mathlib.GroupTheory.Index

/-!
# Milne, Class Field Theory, Section III.5, Step 5

Let `ord : Kˣ → Z` be the normalized valuation.  Milne uses its surjectivity
and the identity `ker(ord) = U_K` to classify the finite-index subgroups
containing `U_K`: they are exactly the inverse images of `n Z`.  We prove the
corresponding group-theoretic statement for an arbitrary surjective additive
homomorphism to `Z`.
-/

namespace Towers.CField.LExist

universe u

/-- Every subgroup containing the kernel of a homomorphism to `Z` is the
inverse image of `n Z` for some natural number `n`. -/
theorem subgroup_comap_zmultiples
    {A : Type u} [AddCommGroup A]
    (ord : A →+ ℤ) (I : AddSubgroup A) (hker : ord.ker ≤ I) :
    ∃ n : ℕ, I = (AddSubgroup.zmultiples (n : ℤ)).comap ord := by
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic (I.map ord)
  refine ⟨a.natAbs, ?_⟩
  calc
    I = I ⊔ ord.ker := (sup_eq_left.mpr hker).symm
    _ = (I.map ord).comap ord := (AddSubgroup.comap_map_eq ord I).symm
    _ = (AddSubgroup.closure {a}).comap ord := congrArg (fun J ↦ J.comap ord) ha
    _ = (AddSubgroup.zmultiples a).comap ord := by
      rw [AddSubgroup.zmultiples_eq_closure]
    _ = (AddSubgroup.zmultiples (a.natAbs : ℤ)).comap ord := by
      rw [Int.zmultiples_natAbs]

/-- In the finite-index case the integer in the preceding classification is
positive.  Equivalently, `n` cannot be zero. -/
theorem comap_zmultiples_ker
    {A : Type u} [AddCommGroup A]
    (ord : A →+ ℤ) (hord : Function.Surjective ord)
    (I : AddSubgroup A) [I.FiniteIndex] (hker : ord.ker ≤ I) :
    ∃ n : ℕ, n ≠ 0 ∧ I = (AddSubgroup.zmultiples (n : ℤ)).comap ord := by
  obtain ⟨n, hI⟩ := subgroup_comap_zmultiples ord I hker
  refine ⟨n, ?_, hI⟩
  intro hn
  have hindex : I.index = n := by
    rw [hI, (AddSubgroup.zmultiples (n : ℤ)).index_comap_of_surjective hord,
      Int.index_zmultiples]
    simp
  rw [hn] at hindex
  exact AddSubgroup.FiniteIndex.index_ne_zero hindex

end Towers.CField.LExist

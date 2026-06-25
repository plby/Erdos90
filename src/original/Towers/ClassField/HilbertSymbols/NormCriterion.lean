import Towers.ClassField.Shifting.GroupPeriodicityOdd

/-!
# Milne, Class Field Theory, Section III.4, Step 1: norm criterion

For a cyclic group, Milne identifies degree-zero Tate cohomology with second
cohomology by periodicity.  Under this identification, a class represented by
an invariant element vanishes exactly when that representative lies in the
image of the norm.  This is the representation-theoretic core of the first
boxed equivalence in Step 1.
-/

namespace Towers.CField.HSymbol

open CategoryTheory Representation
open Shifting

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]

/-- **Section III.4, Step 1, cyclic norm-vanishing criterion.** The degree-two
periodicity class of an invariant representative is zero if and only if that
representative is in the image of the norm from coinvariants. -/
theorem cyclic_periodicity_norm
    (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (b : A.ρ.invariants) :
    tateCohomologyTwo A g hg
          (Submodule.Quotient.mk b) = 0 ↔
      b ∈ LinearMap.range (normCoinvariantsInvariants A) := by
  let e := tateCohomologyTwo A g hg
  constructor
  · intro h
    have hq : (Submodule.Quotient.mk b : tateCohomologyZero A) = 0 := by
      apply e.injective
      simpa [e] using h
    exact (Submodule.Quotient.mk_eq_zero _).mp hq
  · intro hb
    have hq : (Submodule.Quotient.mk b : tateCohomologyZero A) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hb
    rw [hq, map_zero]

end

end Towers.CField.HSymbol

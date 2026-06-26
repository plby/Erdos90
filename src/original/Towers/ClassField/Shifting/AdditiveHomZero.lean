import Mathlib.GroupTheory.OrderOfElement
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Towers.ClassField.Shifting.LowTateCohomology

/-!
# Milne, Class Field Theory, Lemma II.3.3(b)

This file proves the ordinary-cohomology assertion in part (b): a finite
group has no nonzero homomorphism to the torsion-free additive group `ℤ`, so
`H¹(G, ℤ) = 0` for the trivial action.

The companion identification `H_T⁰(G, ℤ) ≃ ZMod |G|` uses the low Tate group
defined in `Section3.Basic` and will be added separately.
-/

namespace Towers.CField.Shifting

open CategoryTheory

/-- Every additive homomorphism from a finite group to `ℤ` is zero. -/
theorem additive_int_zero (G : Type) [AddGroup G] [Finite G]
    (f : G →+ ℤ) : f = 0 := by
  ext x
  obtain ⟨n, hn, hnx⟩ := (isOfFinAddOrder_of_finite x).exists_nsmul_eq_zero
  have hfx := congrArg f hnx
  simp only [map_nsmul, map_zero] at hfx
  have hmul : (n : ℤ) * f x = 0 := by simpa [nsmul_eq_mul] using hfx
  exact (mul_eq_zero.mp hmul).resolve_left (by exact_mod_cast hn.ne')

/-- **Lemma II.3.3(b).** For a finite group acting trivially on `ℤ`, first
group cohomology vanishes. -/
theorem cohomology_trivial_int
    (G : Type) [Group G] [Finite G] :
    Limits.IsZero (groupCohomology (Rep.trivial ℤ G ℤ) 1) := by
  letI : Subsingleton (Additive G →+ ℤ) :=
    ⟨fun f g ↦ by rw [additive_int_zero (Additive G) f,
      additive_int_zero (Additive G) g]⟩
  exact Limits.IsZero.of_iso (ModuleCat.isZero_of_subsingleton _)
    (groupCohomology.H1IsoOfIsTrivial (Rep.trivial ℤ G ℤ))

end Towers.CField.Shifting

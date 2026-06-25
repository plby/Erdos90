import Mathlib.RepresentationTheory.Coinvariants
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Milne, Class Field Theory, Section II.3: low Tate cohomology

For a representation of a finite group, the norm is constant on coinvariant
classes and takes values in the invariants.  The resulting map
`A_G → A^G` gives the two exceptional Tate cohomology groups:

* `H_T⁰(G, A) = A^G / N(A)`;
* `H_T⁻¹(G, A) = ker(A_G → A^G)`.

Together with Mathlib's ordinary group cohomology and group homology, these
are the four cases in Milne's definition.  A uniform integer-indexed Tate
cohomology functor and its bi-infinite long exact sequence are not currently
available in Mathlib.
-/

namespace Submission.CField.Shifting

universe u

open Representation

noncomputable section

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- The norm map from coinvariants to invariants.  This is the middle map
`H₀(G,A) → H⁰(G,A)` in Milne's defining exact sequence for Tate cohomology. -/
noncomputable def normCoinvariantsInvariants (A : Rep k G) :
    A.ρ.Coinvariants →ₗ[k] A.ρ.invariants :=
  Coinvariants.lift A.ρ
    (A.ρ.norm.codRestrict A.ρ.invariants fun x ↦ by
      rw [mem_invariants]
      exact fun g ↦ A.ρ.self_norm_apply g x)
    fun g ↦ LinearMap.ext fun x ↦ Subtype.ext (A.ρ.norm_self_apply g x)

@[simp]
theorem coinvariants_invariants_mk (A : Rep k G) (x : A) :
    normCoinvariantsInvariants A (Coinvariants.mk A.ρ x) =
      ⟨A.ρ.norm x, fun g ↦ A.ρ.self_norm_apply g x⟩ :=
  rfl

/-- Milne's `H_T⁰(G,A) = A^G / N(A)`. -/
abbrev tateCohomologyZero (A : Rep k G) :=
  A.ρ.invariants ⧸ LinearMap.range (normCoinvariantsInvariants A)

/-- Milne's `H_T⁻¹(G,A) = ker(N) / I_G A`, expressed as the kernel of the
induced norm map from coinvariants to invariants. -/
abbrev tateCohomologyOne (A : Rep k G) :=
  LinearMap.ker (normCoinvariantsInvariants A)

end

end Submission.CField.Shifting

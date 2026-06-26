import Mathlib.Algebra.Exact
import Towers.ClassField.Shifting.LowTateCohomology

/-!
# Class Field Theory, Chapter II, Section 3: the norm exact sequence

The exceptional Tate groups are the kernel and cokernel of the norm from
coinvariants to invariants.  This file packages the displayed exact sequence

`0 → H_T⁻¹(G,A) → H₀(G,A) → H⁰(G,A) → H_T⁰(G,A) → 0`.
-/

namespace Towers.CField.Shifting

open Representation

noncomputable section

universe u

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

/-- The inclusion of degree-minus-one Tate cohomology into coinvariants. -/
noncomputable def tateCohomologyInclusion (A : Rep k G) :
    tateCohomologyOne A →ₗ[k] A.ρ.Coinvariants :=
  (LinearMap.ker (normCoinvariantsInvariants A)).subtype

/-- The quotient from invariants onto degree-zero Tate cohomology. -/
noncomputable def tateCohomologyProjection (A : Rep k G) :
    A.ρ.invariants →ₗ[k] tateCohomologyZero A :=
  (LinearMap.range (normCoinvariantsInvariants A)).mkQ

/-- The first map in Milne's norm sequence is injective. -/
theorem tate_inclusion_injective (A : Rep k G) :
    Function.Injective (tateCohomologyInclusion A) :=
  Submodule.injective_subtype _

/-- Exactness of the norm sequence at coinvariants. -/
theorem exact_cohomology_inclusion (A : Rep k G) :
    Function.Exact (tateCohomologyInclusion A)
      (normCoinvariantsInvariants A) :=
  LinearMap.exact_subtype_ker_map (normCoinvariantsInvariants A)

/-- Exactness of the norm sequence at invariants. -/
theorem exact_cohomology_projection (A : Rep k G) :
    Function.Exact (normCoinvariantsInvariants A)
      (tateCohomologyProjection A) :=
  LinearMap.exact_map_mkQ_range (normCoinvariantsInvariants A)

/-- The last map in Milne's norm sequence is surjective. -/
theorem tate_projection_surjective (A : Rep k G) :
    Function.Surjective (tateCohomologyProjection A) :=
  Submodule.mkQ_surjective _

/-- All four assertions comprising Milne's displayed five-term norm exact
sequence. -/
theorem tate_five_exact (A : Rep k G) :
    Function.Injective (tateCohomologyInclusion A) ∧
      Function.Exact (tateCohomologyInclusion A)
        (normCoinvariantsInvariants A) ∧
      Function.Exact (normCoinvariantsInvariants A)
        (tateCohomologyProjection A) ∧
      Function.Surjective (tateCohomologyProjection A) :=
  ⟨tate_inclusion_injective A,
    exact_cohomology_inclusion A,
    exact_cohomology_projection A,
    tate_projection_surjective A⟩

end

end Towers.CField.Shifting

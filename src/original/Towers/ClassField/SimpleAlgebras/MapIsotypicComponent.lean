import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Milne, Class Field Theory, Proposition IV.1.7

This file records the functoriality and decomposition of isotypic components,
and Milne's characterization of submodules stable under every endomorphism.
-/

namespace Towers.CField.SAlgebr

universe u v w

variable {R : Type u} {M : Type v} {N S : Type w}
variable [Ring R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable [AddCommGroup S] [Module R S]

/-- A module homomorphism maps the isotypic component of type `S` into the
isotypic component of the same type. -/
theorem isotypic_component [IsSimpleModule R S] (f : M →ₗ[R] N) :
    (isotypicComponent R M S).map f ≤ isotypicComponent R N S :=
  Submodule.map_le_iff_le_comap.mpr
    (LinearMap.le_comap_isotypicComponent S f)

/-- The isotypic components of a semisimple module are independent. -/
theorem isotypicComponents_independent :
    sSupIndep (isotypicComponents R M) :=
  sSupIndep_isotypicComponents R M

/-- The isotypic components of a semisimple module span the whole module. -/
theorem isotypic_components_s [IsSemisimpleModule R M] :
    sSup (isotypicComponents R M) = ⊤ :=
  sSup_isotypicComponents R M

/-- **Proposition IV.1.7.** A submodule is stable under every endomorphism if
and only if it is a sum of isotypic components. -/
theorem fully_isotypic_components
    [IsSemisimpleModule R M] (W : Submodule R M) :
    W.IsFullyInvariant ↔
      ∃ C ⊆ isotypicComponents R M, W = sSup C :=
  isFullyInvariant_iff_sSup_isotypicComponents

end Towers.CField.SAlgebr

import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

/-!
# Milne, Class Field Theory, Statement II.2.3

Group homology is functorial in the coefficient module.  Mathlib constructs it
from the canonical inhomogeneous chain complex, so the induced map does not
depend on a choice of projective resolution or of a lift between resolutions.
-/

namespace Towers.CField.TCohomo

open CategoryTheory

variable (G : Type) [Group G]

/-- **Statement II.2.3.** For every degree `r`, integral group homology is a
functor from `G`-modules to abelian groups (presented as `ℤ`-modules). -/
noncomputable def groupHomologyFunctor (r : ℕ) : Rep ℤ G ⥤ ModuleCat ℤ :=
  groupHomology.functor ℤ G r

@[simp]
theorem homology_functor_obj (r : ℕ) (M : Rep ℤ G) :
    (groupHomologyFunctor G r).obj M = groupHomology M r :=
  rfl

/-- The morphism furnished by Statement II.2.3 is the standard map on group
homology induced by the coefficient homomorphism. -/
@[simp]
theorem group_homology_functor (r : ℕ) {M N : Rep ℤ G} (f : M ⟶ N) :
    (groupHomologyFunctor G r).map f =
      groupHomology.map (MonoidHom.id G) f r :=
  rfl

/-- The induced map of an identity coefficient homomorphism is the identity. -/
theorem group_homology_id (r : ℕ) (M : Rep ℤ G) :
    groupHomology.map (MonoidHom.id G) (𝟙 M) r =
      𝟙 (groupHomology M r) := by
  exact (groupHomologyFunctor G r).map_id M

/-- Induced homology maps respect composition; in particular they are
independent of how a coefficient homomorphism is factored. -/
theorem group_homology_comp (r : ℕ) {M N P : Rep ℤ G}
    (f : M ⟶ N) (g : N ⟶ P) :
    groupHomology.map (MonoidHom.id G) (f ≫ g) r =
      groupHomology.map (MonoidHom.id G) f r ≫
        groupHomology.map (MonoidHom.id G) g r := by
  exact (groupHomologyFunctor G r).map_comp f g

end Towers.CField.TCohomo

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.DenseEmbedding

/-!
# Milne, Class Field Theory, Proposition III.4.3: density step

The last step in Milne's proof is purely topological.  A continuous character
which is zero on the image of the local Artin map is zero everywhere because
that image is dense.  This file states and proves that implication for an
arbitrary dense map.
-/

namespace Towers.CField.HSymbol

universe u v w

/-- A continuous additive character into a Hausdorff topological group which
vanishes on a dense image is the zero character. -/
theorem continuous_monoid_range
    {X : Type u} {G : Type v} {A : Type w}
    [AddMonoid G] [AddMonoid A] [TopologicalSpace G] [TopologicalSpace A]
    [T2Space A]
    (φ : X → G) (hφ : DenseRange φ) (χ : G →+ A)
    (hχ : Continuous χ) (hzero : ∀ x, χ (φ x) = 0) :
    χ = 0 := by
  apply AddMonoidHom.ext
  intro g
  have heq : (χ : G → A) = fun _ ↦ 0 :=
    hφ.equalizer hχ continuous_const (by
      funext x
      exact hzero x)
  exact congr_fun heq g

end Towers.CField.HSymbol

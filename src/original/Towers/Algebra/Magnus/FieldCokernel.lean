import Towers.Algebra.Magnus.IntegralCokernel
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Scalar extension of the graded Magnus map

For a field `K`, the lower-central quotient in the source of the graded
Magnus map is understood after extension of scalars from `ℤ` to `K`.
The integral Hall basis gives a basis of this scalar extension, and the
Magnus map sends its basis vectors to the corresponding Hall leading
polynomials.  Its cokernel is therefore a vector space, hence torsion-free.
-/

namespace EChapma
namespace FCokern

open Towers
open Towers.TBluepr

universe u v

variable {K : Type u} {X : Type v}
  [Field K]
  [Fintype X] [DecidableEq X] [Encodable X]

/-- Extension of scalars of the zero-based lower-central layer
`γ_(n+1)(F)/γ_(n+2)(F)` from `ℤ` to `K`. -/
abbrev ScalarExtendedLayer
    (K : Type u) (X : Type v) [CommRing K]
    (n : ℕ) :=
  TensorProduct ℤ K
    (Additive
      (LowerGradedLayer (FreeGroup X) n))

/-- The Hall basis of a lower-central layer after extension of scalars. -/
noncomputable def scalarExtendedBasis
    (K : Type u) (X : Type v) [CommRing K]
    [Fintype X] [DecidableEq X] [Encodable X]
    (n : ℕ) :
    Module.Basis
      (Towers.HallTree.BasicIndex (α := X) (n + 1))
      K
      (ScalarExtendedLayer K X n) :=
  (IMagnus.lowerCentralBasis (X := X) n).baseChange K

/-- The degree-`n+1` Magnus map after scalar extension, expressed in Hall
coordinates. -/
noncomputable def scalarExtendedMagnus
    (K : Type u) (X : Type v) [CommRing K]
    [Fintype X] [DecidableEq X] [Encodable X]
    (n : ℕ) :
    ScalarExtendedLayer K X n →ₗ[K]
      AssociativeHomogeneousWords K X (n + 1) :=
  (Finsupp.linearCombination K
      (fun i : Towers.HallTree.BasicIndex (α := X) (n + 1) =>
        Towers.HallTree.associativeRepWeight K
          (Towers.HallTree.indexedBasicTree i)
          (Towers.HallTree.indexed_tree_weight i))).comp
    (scalarExtendedBasis K X n).repr.toLinearMap

/-- A scalar-extended Hall basis vector maps to its Hall leading polynomial. -/
@[simp]
theorem scalar_extended_magnus
    (n : ℕ)
    (i : Towers.HallTree.BasicIndex (α := X) (n + 1)) :
    scalarExtendedMagnus K X n
        (scalarExtendedBasis K X n i) =
      Towers.HallTree.associativeRepWeight K
        (Towers.HallTree.indexedBasicTree i)
        (Towers.HallTree.indexed_tree_weight i) := by
  simp [scalarExtendedMagnus]

/-- On a pure tensor of an integral Hall class, the scalar-extended map is
the corresponding Hall leading polynomial. -/
theorem scalar_extended_tmul
    (n : ℕ)
    (i : Towers.HallTree.BasicIndex (α := X) (n + 1)) :
    scalarExtendedMagnus K X n
        ((1 : K) ⊗ₜ[ℤ]
          IMagnus.lowerCentralBasis (X := X) n i) =
      Towers.HallTree.associativeRepWeight K
        (Towers.HallTree.indexedBasicTree i)
        (Towers.HallTree.indexed_tree_weight i) := by
  rw [← Module.Basis.baseChange_apply]
  exact scalar_extended_magnus (K := K) (X := X) n i

/-- Finite-alphabet, scalar-extended form of Efrat--Chapman, Corollary 2.4,
field case: the cokernel is torsion-free over the coefficient field. -/
theorem scalar_extended_cokernel
    (n : ℕ) :
    Module.IsTorsionFree K
      (AssociativeHomogeneousWords K X (n + 1) ⧸
        LinearMap.range (scalarExtendedMagnus K X n)) :=
  cokernel_torsion_field
    (scalarExtendedMagnus K X n)

end FCokern
end EChapma
